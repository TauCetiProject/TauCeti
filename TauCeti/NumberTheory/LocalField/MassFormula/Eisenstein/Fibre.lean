/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Eisenstein coefficient fibres over balls of uniformizers

Let `L / K` be an extension of nonarchimedean local fields with ramification index `n`. When a
ball `v_L(z - c) ≥ r` is centred at a uniformizer `c` and has order `r ≥ 2`, every root in the
ball is a uniformizer. A monic polynomial over `𝒪[K]` of degree `e(L/K)` with a uniformizer as a
root is Eisenstein, so the part of the Eisenstein region whose polynomial has a root in the ball
is the image of the set of all integral coefficient vectors whose polynomial has a root there.
This is the form of the fibre on which the local root criterion at the centre and the volume
computation in power-basis coordinates operate.

## Main results

* `TauCeti.eisensteinSet_inter_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal_eq_image`: over
  a ball of order at least `2` centred at a uniformizer, the fibre of the Eisenstein region is the
  image of the corresponding integral coefficient fibre.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3, Lemmas 2–3.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing

namespace TauCeti

open TauCeti.Polynomial
  (monicOfCoeff map_monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Coefficient fibres at a uniformizer are integral.** Let `n = e(L/K)`, let `c` be a
uniformizer of `L`, and let `1 < r`. A coefficient vector in the Eisenstein region whose
polynomial has a root in the ball `v_L(z - c) ≥ r` is the coefficient vector of a monic polynomial
over `𝒪[K]` with a root in that ball. Conversely, every root in that ball is a uniformizer, so
every monic polynomial of degree `e(L/K)` over `𝒪[K]` with such a root is Eisenstein. Hence this
part of the Eisenstein region is the image of the corresponding set of integral coefficient
vectors. -/
theorem eisensteinSet_inter_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal_eq_image
    {n : ℕ} (hn : ramificationIndex K L = n) {r : ℕ} (hr : 1 < r) {c : 𝒪[L]}
    (hc : addVal 𝒪[L] c = 1) :
    eisensteinSet K n ∩ {a | ∃ z : 𝒪[L],
        aeval (z : L) (monicOfCoeff a) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} =
      (fun b : Fin n → 𝒪[K] ↦ fun i ↦ (b i : K)) '' {b | ∃ z : 𝒪[L],
        aeval z (monicOfCoeff b) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} := by
  -- Fix the subring algebra so root transport stays inside `L`.
  let : Algebra 𝒪[L] L := Algebra.ofSubsemiring (R := L) (A := L) 𝒪[L]
  have : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl
  -- Evaluating at `z` commutes with extending the coefficients from `𝒪[K]` to `K`.
  have hroot (b : Fin n → 𝒪[K]) (z : 𝒪[L]) :
      aeval (z : L) (monicOfCoeff fun i ↦ (b i : K)) = 0 ↔ aeval z (monicOfCoeff b) = 0 := by
    have hmap : (monicOfCoeff fun i ↦ (b i : K)) = (monicOfCoeff b).map (algebraMap 𝒪[K] K) := by
      rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring]
    rw [hmap, aeval_map_algebraMap]
    exact aeval_algebraMap_eq_zero_iff_of_injective (IsFractionRing.injective 𝒪[L] L)
  -- A root in the ball is a uniformizer, since `v_L(c) = 1 < r ≤ v_L(z - c)`.
  have hirr {z : 𝒪[L]} (hz : (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)) : Irreducible z := by
    refine IsDiscreteValuationRing.addVal_eq_one_iff_irreducible.1 ?_
    have hlt : addVal 𝒪[L] c < addVal 𝒪[L] (z - c) :=
      hc ▸ lt_of_lt_of_le (by exact_mod_cast hr) hz
    rw [← add_sub_cancel c z, (addVal 𝒪[L]).map_add_eq_of_lt_left hlt, hc]
  ext a
  constructor
  · rintro ⟨ha, z, hz, hzr⟩
    let b : Fin n → 𝒪[K] := fun i ↦ ⟨a i, mem_integerBox.1 (eisensteinSet_subset_integerBox n ha) i⟩
    exact ⟨b, ⟨z, (hroot b z).1 hz, hzr⟩, rfl⟩
  · rintro ⟨b, ⟨z, hz, hzr⟩, rfl⟩
    refine ⟨mem_eisensteinSet_iff_exists_isEisensteinAt.2 ⟨monicOfCoeff b, ?_, ?_⟩,
      z, (hroot b z).2 hz, hzr⟩
    · rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring]
    · refine isEisensteinAt_of_isRoot_of_irreducible ?_ ((natDegree_monicOfCoeff b).trans hn.symm)
        (hirr hzr) (by rwa [IsRoot, eval_map_algebraMap])
      rw [(monic_monicOfCoeff b).leadingCoeff]
      exact Ideal.one_notMem _

end TauCeti
