/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationGroup
public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.RingTheory.Ideal.RamificationGroup

/-!
# Global and local ramification groups

Let `L/K` be an extension of number fields, `v` a finite place of `K`, and `w` a finite place of
`L` above `v`. The decomposition group of `w`, the stabilizer of `w` in `Aut(L/K)`, acts on the
completion `L_w` through `decompositionHom v w`. This file proves that this action matches the
two ramification filtrations: the global ramification groups `G_i` of the prime `w` of `𝓞 L`,
cut out by congruences modulo `w ^ (i + 1)`, and the lower-numbering ramification groups of the
local extension `L_w/K_v`, cut out by congruences modulo the powers of the maximal ideal of the
ring of integers `𝒪[L_w]`.

The comparison is an equality of subgroups along the named map `decompositionHom v w`, not an
abstract isomorphism, so that elements can be moved across it. It rests on two facts. An element
of `𝓞 L` lies in `w ^ n` exactly when its image in `L_w` has valuation at most `exp (-n)`, so the
global congruences are the local ones restricted to `𝓞 L`. Conversely `𝓞 L` is dense in `𝒪[L_w]`
modulo every power of the maximal ideal, and the action of the decomposition group preserves the
valuation, so a congruence that holds on `𝓞 L` holds on all of `𝒪[L_w]`.

For `L/K` Galois, `decompositionHom v w` is an isomorphism onto `Aut(L_w/K_v)`, and the global
and local ramification groups have the same orders. In particular the global wild inertia group
`G_1` of `w` is trivial exactly when `L_w/K_v` is tamely ramified, that is, when the residue
characteristic does not divide `e(w/v)`. The reading on the different exponent is in
`TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Tame`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.mem_ramificationGroup_iff_decompositionHom_mem`: an element
  of the decomposition group of `w` lies in the `i`-th global ramification group of `w` exactly
  when its action on `L_w` lies in the `i`-th local ramification group.
* `IsDedekindDomain.HeightOneSpectrum.ramificationGroup_stabilizer_eq_comap_decompositionHom`: the
  same statement as an equality of subgroups of the decomposition group.
* `IsDedekindDomain.HeightOneSpectrum.map_ramificationGroup_decompositionHom`: for `L/K`
  Galois, `decompositionHom v w` carries the global ramification groups onto the local ones.
* `IsDedekindDomain.HeightOneSpectrum.card_ramificationGroup_eq_card_lowerRamificationGroup`: for
  `L/K` Galois, the global and local ramification groups have the same orders.
* `IsDedekindDomain.HeightOneSpectrum.ramificationGroup_one_eq_bot_iff_isTamelyRamified` and
  `ramificationGroup_one_eq_bot_iff_natCast_ramificationIdx_ne_zero`: for `L/K` Galois, `G_1` is
  trivial exactly when `w` is tamely ramified, read on the completion and on the ramification
  index in the residue field of `v`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1.
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §9.
-/

public section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel WithZero
open scoped NumberField Pointwise AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]

/-- **The global and local ramification groups agree.** An element `σ` of the decomposition group
of `w` lies in the `i`-th ramification group of the prime `w` of `𝓞 L` exactly when its continuous
extension to `L_w` lies in the `i`-th lower-numbering ramification group of `L_w/K_v`. -/
theorem mem_ramificationGroup_iff_decompositionHom_mem (i : ℕ)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    (σ : L ≃ₐ[K] L) ∈ w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ↔
      decompositionHom v w σ ∈ TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i := by
  rw [Ideal.mem_ramificationGroup_iff,
    TauCeti.LocalFieldsRamification.lowerRamificationGroup_def,
    TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff]
  simp_rw [mem_maximalIdeal_integer_pow_iff, w.mem_asIdeal_pow_iff_valued_algebraMap_le (K := L),
    map_sub, AddSubgroupClass.coe_sub, AlgEquiv.coe_smul_integerRing]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · -- approximate `y` by an element `a` of `𝓞 L` modulo the `(i + 1)`-st power of the maximal
    -- ideal; the action moves `y - a` by no more than that power, and moves `a` by `h`
    obtain ⟨a, ha⟩ := w.exists_valued_sub_le (K := L)
      (w.integerEquivAdicCompletionIntegers (K := L) y) (i + 1)
    rw [coe_integerEquivAdicCompletionIntegers] at ha
    have hσa : Valued.v (decompositionHom v w σ (algebraMap (𝓞 L) (w.adicCompletion L) a) -
        algebraMap (𝓞 L) (w.adicCompletion L) a) ≤ exp (-((i + 1 : ℕ) : ℤ)) := by
      rw [decompositionHom_algebraMap_ringOfIntegers]
      exact h a
    have hσya : Valued.v (decompositionHom v w σ
        ((y : w.adicCompletion L) - algebraMap (𝓞 L) (w.adicCompletion L) a)) ≤
          exp (-((i + 1 : ℕ) : ℤ)) := by
      rwa [valued_decompositionHom]
    rw [map_sub] at hσya
    have hsplit : decompositionHom v w σ (y : w.adicCompletion L) - y =
        (decompositionHom v w σ y - decompositionHom v w σ (algebraMap (𝓞 L) _ a)) +
          (decompositionHom v w σ (algebraMap (𝓞 L) _ a) - algebraMap (𝓞 L) _ a) -
            (y - algebraMap (𝓞 L) (w.adicCompletion L) a) := by
      ring
    rw [hsplit]
    exact Valuation.map_sub_le _ (Valuation.map_add_le _ hσya hσa) ha
  · have hx : Valued.v (decompositionHom v w σ (algebraMap (𝓞 L) (w.adicCompletion L) x) -
        algebraMap (𝓞 L) (w.adicCompletion L) x) ≤ exp (-((i + 1 : ℕ) : ℤ)) :=
      h ⟨_, algebraMap_mem_integer_adicCompletion w x⟩
    rwa [decompositionHom_algebraMap_ringOfIntegers] at hx

/-- **The global ramification groups are the local ones, pulled back along `decompositionHom`.**
Inside the decomposition group of `w`, the `i`-th ramification group of `w` is the preimage of the
`i`-th lower-numbering ramification group of `L_w/K_v`. -/
theorem ramificationGroup_stabilizer_eq_comap_decompositionHom (i : ℕ) :
    w.asIdeal.ramificationGroup (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) i =
      (TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i).comap (decompositionHom v w) := by
  ext σ
  rw [← Ideal.ramificationGroup_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
    mem_ramificationGroup_iff_decompositionHom_mem v]

variable [IsGalois K L]

variable (w) in
/-- **The decomposition group carries the global ramification groups onto the local ones.** For
`L/K` Galois, the image of the `i`-th ramification group of `w` in `Aut(L_w/K_v)` is the `i`-th
lower-numbering ramification group of `L_w/K_v`. -/
theorem map_ramificationGroup_decompositionHom (i : ℕ) :
    (w.asIdeal.ramificationGroup (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) i).map
        (decompositionHom v w) =
      TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i := by
  rw [ramificationGroup_stabilizer_eq_comap_decompositionHom v]
  exact Subgroup.map_comap_eq_self_of_surjective (decompositionHom_surjective v w) _

variable (w) in
/-- **The global and local ramification groups have the same order.** For `L/K` Galois, the
`i`-th ramification group of `w` has as many elements as the `i`-th lower-numbering ramification
group of `L_w/K_v`. -/
theorem card_ramificationGroup_eq_card_lowerRamificationGroup (i : ℕ) :
    Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) =
      Nat.card (TauCeti.LocalFieldsRamification.lowerRamificationGroup
        (v.adicCompletion K) (w.adicCompletion L) i) := by
  rw [← map_ramificationGroup_decompositionHom v w i, ← Ideal.ramificationGroup_subgroupOf]
  exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe
    (w.asIdeal.ramificationGroup_le_stabilizer i)).symm.trans
      (Subgroup.equivMapOfInjective _ _ (decompositionHom_injective v w))).toEquiv

variable (w) in
/-- **Wild inertia is trivial exactly at tame primes.** For `L/K` Galois, the first ramification
group `G_1` of `w` is trivial if and only if the completed extension `L_w/K_v` is tamely
ramified. -/
theorem ramificationGroup_one_eq_bot_iff_isTamelyRamified :
    w.asIdeal.ramificationGroup (L ≃ₐ[K] L) 1 = ⊥ ↔
      TauCeti.IsTamelyRamified (v.adicCompletion K) (w.adicCompletion L) := by
  rw [← Subgroup.card_eq_one, card_ramificationGroup_eq_card_lowerRamificationGroup v w 1,
    Subgroup.card_eq_one, Nat.cast_one,
    TauCeti.LocalFieldsRamification.lowerRamificationGroup_one_eq_bot_iff_isTamelyRamified]

variable (w) in
/-- For `L/K` Galois, the first ramification group `G_1` of `w` is trivial if and only if the
ramification index `e(w/v)` is nonzero in the residue field of `v`, that is, not divisible by
the residue characteristic. -/
theorem ramificationGroup_one_eq_bot_iff_natCast_ramificationIdx_ne_zero :
    w.asIdeal.ramificationGroup (L ≃ₐ[K] L) 1 = ⊥ ↔
      ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 K ⧸ v.asIdeal) ≠ 0 :=
  (ramificationGroup_one_eq_bot_iff_isTamelyRamified v w).trans
    (isTamelyRamified_adicCompletion_iff v w)

end IsDedekindDomain.HeightOneSpectrum
