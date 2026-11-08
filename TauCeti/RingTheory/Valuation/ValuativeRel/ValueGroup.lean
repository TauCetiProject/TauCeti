/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Valued extensions with unchanged value group

If the map on value groups of a valued extension is surjective, it is an order isomorphism.
Thus discreteness and rank at most one pass to the extension. Irreducible elements of the base
valuation ring remain irreducible in the extended valuation ring. These statements
apply to unramified algebraic extensions and to completions without requiring finite degree.
-/

public section

open ValuativeRel

/-- If every value in an extension is attained on the base, its value-group map is onto. -/
theorem ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq
    {A B : Type*} [CommRing A] [DivisionRing B] [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] [ValuativeExtension A B]
    (h : ∀ x : B, ∃ r : A, algebraMap A B r =ᵥ x) :
    Function.Surjective (mapValueGroupWithZero A B) := by
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  obtain ⟨r, hr⟩ := h x
  exact ⟨valuation A r, by
    rw [mapValueGroupWithZero_valuation]
    exact (valuation B).veq_iff_eq.mp hr⟩

namespace ValuativeRel

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A valued extension with surjective map on value groups preserves discreteness. -/
theorem IsDiscrete.of_surjective_mapValueGroupWithZero [IsDiscrete A]
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero A B)) : IsDiscrete B := by
  obtain ⟨γ, hγ, hmax⟩ := IsDiscrete.has_maximal_element (R := A)
  have hm := ValuativeExtension.mapValueGroupWithZero_strictMono (A := A) (B := B)
  refine ⟨ValuativeExtension.mapValueGroupWithZero A B γ, by simpa using hm hγ, ?_⟩
  intro δ hδ
  obtain ⟨δ, rfl⟩ := h δ
  exact hm.monotone (hmax δ (hm.lt_iff_lt.mp (by simpa using hδ)))

/-- A valued extension with surjective map on value groups preserves rank at most one. -/
theorem IsRankLeOne.of_surjective_mapValueGroupWithZero [IsRankLeOne A]
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero A B)) : IsRankLeOne B := by
  let e : ValueGroupWithZero A ≃*o ValueGroupWithZero B :=
    ⟨MulEquiv.ofBijective (ValuativeExtension.mapValueGroupWithZero A B)
      ⟨ValuativeExtension.mapValueGroupWithZero_strictMono.injective, h⟩,
      ValuativeExtension.mapValueGroupWithZero_strictMono.le_iff_le⟩
  obtain ⟨f⟩ := IsRankLeOne.nonempty (R := A)
  exact ⟨⟨f.emb.comp e.symm.toMonoidWithZeroHom, f.strictMono.comp e.symm.strictMono⟩⟩

end ValuativeRel

namespace Irreducible

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- An irreducible element remains irreducible in a valued extension with unchanged value group.
Neither valuation ring needs to be assumed discrete. -/
theorem algebraMap_integer_of_surjective_mapValueGroupWithZero {π : (valuation K).integer}
    (hπ : Irreducible π)
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero K L)) :
    Irreducible (algebraMap (valuation K).integer (valuation L).integer π) := by
  let π' := algebraMap (valuation K).integer (valuation L).integer π
  have he := ValuativeRel.isEquiv ((valuation L).comap (algebraMap K L)) (valuation K)
  have hπ' : valuation L (π' : L) < 1 := by
    rw [TauCeti.coe_algebraMap_integerRing]
    exact he.lt_one_iff_lt_one.mpr (Valuation.integer.v_irreducible_lt_one hπ)
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π'
  · intro hz
    have hz' : algebraMap K L (π : K) = 0 := by
      simpa [π', TauCeti.coe_algebraMap_integerRing] using congrArg Subtype.val hz
    exact hπ.ne_zero (Subtype.ext <| (algebraMap K L).injective (by simpa using hz'))
  · apply le_antisymm
    · intro x hx
      have hxv := (valuation L).mem_maximalIdeal_iff.mp hx
      obtain ⟨γ, hγ⟩ := h (valuation L (x : L))
      obtain ⟨r, rfl⟩ := valuation_surjective γ
      rw [ValuativeExtension.mapValueGroupWithZero_valuation] at hγ
      have hr : valuation K r < 1 := he.lt_one_iff_lt_one.mp (by simpa [hγ] using hxv)
      have hle : valuation K r ≤ valuation K (π : K) := by
        by_cases hle : valuation K r ≤ valuation K (π : K)
        · exact hle
        have hd : (⟨r, hr.le⟩ : (valuation K).integer) ∣ π :=
          (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr (le_of_not_ge hle)
        have hn : ¬IsUnit (⟨r, hr.le⟩ : (valuation K).integer) :=
          Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hr
        exact (Valuation.integer.integers (valuation K)).dvd_iff_le.mp
          (((hπ.dvd_iff.mp hd).resolve_left hn).dvd)
      have hxπ : valuation L (x : L) ≤ valuation L (π' : L) := by
        rw [TauCeti.coe_algebraMap_integerRing, ← hγ]
        simpa only [Valuation.comap_apply] using (he r (π : K)).mpr hle
      rw [Ideal.mem_span_singleton]
      exact (Valuation.integer.integers (valuation L)).dvd_iff_le.mpr hxπ
    · exact (Ideal.span_singleton_le_iff_mem _).mpr
        ((valuation L).mem_maximalIdeal_iff.mpr hπ')

end Irreducible
