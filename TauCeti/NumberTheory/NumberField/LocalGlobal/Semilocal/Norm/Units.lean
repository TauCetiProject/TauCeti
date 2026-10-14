/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
public import TauCeti.NumberTheory.LocalField.Norm.Unramified.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.DecompositionGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Norm equations in the local étale algebras

For a number-field extension `L/K`, the local norm is the norm of `K_v ⊗[K] L`.
The semilocal comparisons identify its image with products of norms from all completions
above the place, including split algebras and real and complex places.

## Main results

* `TauCeti.mem_range_normUnits_adicCompletion_iff` and
  `TauCeti.mem_range_normUnits_completion_iff`: the local norm range as products of norms.
* `TauCeti.exists_unit_preimages_of_isUnramifiedAt`: a unit has integral unit preimages
  if one completion above the place is unramified.
* `TauCeti.mem_range_normUnits_adicCompletion_of_finrank_eq_one`: every element is a local norm
  if one completion above the place has degree one.
* `TauCeti.pow_mem_range_normUnits_completion`: at an infinite place every `n`-th power is a local
  norm once `n` kills `Gal(L/K)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, (8.4), and Chapter VI, §2.

The local decompositions are `TauCeti.semilocalEquiv` and
`TauCeti.GlobalNumberFields.infiniteSemilocalEquiv`; unit-norm surjectivity is
`TauCeti.map_normUnits_unitFiltration`.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  WithZeroMulInt
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver WithZero

namespace TauCeti

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A unit is a finite local norm exactly when it is a product of norms from the completions
above the place. This includes split local algebras. -/
theorem mem_range_normUnits_adicCompletion_iff (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    a ∈ (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range ↔
      ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
          (w.1.adicCompletion L)ˣ,
        (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) = a :=
  Algebra.mem_range_normUnits_iff_of_algEquiv (semilocalEquiv L v) a

/-- A unit is an infinite local norm exactly when it is a product of norms from the completions
above the place. Real and complex places are both retained. -/
theorem mem_range_normUnits_completion_iff (v : InfinitePlace K) (a : v.Completionˣ) :
    a ∈ (Algebra.normUnits v.Completion (S := v.Completion ⊗[K] L)).range ↔
      ∃ u : (w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completionˣ,
        (∏ᶠ w, Algebra.normUnits v.Completion (u w)) = a :=
  Algebra.mem_range_normUnits_iff_of_algEquiv (GlobalNumberFields.infiniteSemilocalEquiv L v) a

/-- A unit of the base completion is a product of norms of integral units of the completions
above it whenever at least one of those extensions is unramified. -/
theorem exists_unit_preimages_of_isUnramifiedAt (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) (ha : Valued.v (a : v.adicCompletion K) = 1)
    (hU : ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
        (w.1.adicCompletion L)ˣ,
      (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) = a ∧
        ∀ w, Valued.v (u w : w.1.adicCompletion L) = 1 := by
  classical
  obtain ⟨w, hw⟩ := hU
  let : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := hw
  have haU : a ∈ unitFiltration (v.adicCompletion K) 0 := by
    apply (mem_unitFiltration_adicCompletion_iff v).mpr
    refine ⟨ha, ?_⟩
    simpa [ha] using (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_sub
      (a : v.adicCompletion K) 1
  rw [← map_normUnits_unitFiltration (v.adicCompletion K) (w.1.adicCompletion L) 0] at haU
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haU
  refine ⟨Pi.mulSingle w b, ?_, ?_⟩
  · rw [finprod_eq_single _ w]
    · simpa using hba
    · intro w' hw'
      simp [Pi.mulSingle_eq_of_ne hw']
  · intro w'
    by_cases hw' : w' = w
    · subst w'
      simp only [Pi.mulSingle_eq_same]
      exact ((mem_unitFiltration_adicCompletion_iff w.1).mp hb).1
    · simp [Pi.mulSingle_eq_of_ne hw']

/-- **Local norms at a finite place of degree one.** If some completion `L_w` of `L` above the
finite place `v` has degree one over `K_v`, then every element of `K_vˣ` is a norm from the local
étale algebra `K_v ⊗[K] L`. -/
theorem mem_range_normUnits_adicCompletion_of_finrank_eq_one (v : HeightOneSpectrum (𝓞 K))
    (hv : ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (a : (v.adicCompletion K)ˣ) :
    a ∈ (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range := by
  classical
  obtain ⟨w, hw⟩ := hv
  obtain ⟨b, hb⟩ := mem_normGroup_iff.1 (pow_finrank_mem_normGroup (w.1.adicCompletion L) a)
  rw [mem_range_normUnits_adicCompletion_iff]
  refine ⟨Pi.mulSingle w b, ?_⟩
  rw [finprod_eq_single _ w fun w' hw' ↦ by simp [Pi.mulSingle_eq_of_ne hw']]
  ext
  simp [hb, hw]

/-- **`n`-th powers are local norms at an infinite place.** If `n` kills `Gal(L/K)`, then every
`n`-th power of `K_vˣ` is a norm from the local étale algebra `K_v ⊗[K] L`: the local degree
`[L_w : K_v]` is the order of the decomposition group of `w`, a cyclic group of order `1` or `2`,
so it divides `n`, and `a ^ [L_w : K_v]` is the norm of `a`. -/
theorem pow_mem_range_normUnits_completion [IsGalois K L] {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (v : InfinitePlace K) (a : v.Completionˣ) :
    a ^ n ∈ (Algebra.normUnits v.Completion (S := v.Completion ⊗[K] L)).range := by
  classical
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  have : w.LiesOver v := hw ▸ inferInstance
  have hcyc : IsCyclic (MulAction.stabilizer Gal(L/K) w) := by
    by_cases h : w.IsUnramified K
    · have : Subsingleton (MulAction.stabilizer Gal(L/K) w) := by
        rw [h.stabilizer_eq_bot]
        infer_instance
      infer_instance
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card (not_isUnramified_iff_card_stabilizer_eq_two.1 h)
  obtain ⟨k, hk⟩ : Module.finrank v.Completion w.Completion ∣ n := by
    rw [← card_stabilizer_eq_finrank_completion v w, ← IsCyclic.exponent_eq_card]
    exact (Monoid.exponent_dvd_of_monoidHom (Subgroup.subtype _) Subtype.val_injective).trans hn
  obtain ⟨b, hb⟩ := mem_normGroup_iff.1 (pow_finrank_mem_normGroup w.Completion (a ^ k))
  rw [mem_range_normUnits_completion_iff]
  refine ⟨Pi.mulSingle ⟨w, this⟩ b, ?_⟩
  rw [finprod_eq_single _ ⟨w, this⟩ fun w' hw' ↦ by simp [Pi.mulSingle_eq_of_ne hw']]
  ext
  simp [hb, hk, ← pow_mul, mul_comm]

end TauCeti
