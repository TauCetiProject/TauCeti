/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Index
import TauCeti.NumberTheory.LocalField.FiniteExtension.GaloisInduction
import TauCeti.NumberTheory.LocalField.Herbrand.Unramified
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.NumberTheory.LocalField.Norm.Unramified.Basic

/-!
# Norm surjectivity above a ramification break

Surjectivity of the successive graded norms implies surjectivity on an entire unit-filtration
step. The image of the source step is compact, hence closed, and successive approximation
makes it dense in the target step. Thus no choice of an infinite product is needed.

For a Galois extension of prime degree with upper break `t`, this proves
`N(U(L, ψℕ(v))) = U(K,v)` whenever `t < v`. The depths are the canonical integral inverse
Herbrand values, so the result includes wild extensions without removing the Herbrand shift.

For an arbitrary finite Galois extension the same holds above every upper break: if the upper
ramification group `G^v` is trivial at a natural number `v`, then `N(U(L, ψℕ(v))) = U(K,v)`. The
Galois group is solvable, so `L/K` is a tower of Galois steps of prime degree. Along a tower
`L/F/K` with `F/K` Galois, the quotient `Gal(F/K)^v` is the image of `G^v` and the subgroup
`Gal(L/F)^{ψℕ_{F/K}(v)}` is its trace on `Gal(L/F)`, so both vanish; the norm and the integral
inverse Herbrand function are transitive.

## Main results

* `TauCeti.map_normUnits_unitFiltration_after_break`: surjectivity above a prime-degree break.
* `TauCeti.map_normUnits_unitFiltration_psiNat_eq_of_upperRamificationGroup_eq_bot`:
  `N(U(L, ψℕ(v))) = U(K,v)` for every finite Galois extension with `G^v = 1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3, Proposition 5 and its corollaries,
  and §6, Proposition 9.
-/

public section
noncomputable section

open Module TauCeti.LocalFieldsRamification

universe u v

namespace TauCeti

variable {K : Type u} {L : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- Surjectivity of every graded norm at and beyond `v` implies surjectivity of the norm
from `U(L, ψℕ(v))` onto `U(K,v)`. -/
theorem map_normUnits_unitFiltration_eq_of_surjective_normGradedMap (v : ℕ)
    (h : ∀ n, v ≤ n → Function.Surjective (normGradedMap K L n)) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v := by
  let S := (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)
  have hclosed : IsClosed (S : Set Kˣ) :=
    ((isCompact_unitFiltration (K := L) _).image (continuous_normUnits K L)).isClosed
  -- Each successive quotient is exhausted by norms from a subgroup of the fixed source step.
  have hstep (n : ℕ) (hn : v ≤ n) : unitFiltration K n ≤ S ⊔ unitFiltration K (n + 1) := by
    have hindex : (((unitFiltration L (psiNat K L n)).map (Algebra.normUnits K)) ⊔
        unitFiltration K (n + 1)).relIndex (unitFiltration K n) = 1 := by
      rw [relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap,
        MonoidHom.range_eq_top.2 (h n hn), Subgroup.index_top]
    exact (Subgroup.relIndex_eq_one.1 hindex).trans <| sup_le_sup_right
      (Subgroup.map_mono (unitFiltration_antitone ((psiNat_strictMono K L).monotone hn))) _
  exact le_antisymm (map_normUnits_unitFiltration_psiNat_le K L v)
    (unitFiltration_le_of_isClosed_of_le_sup hclosed hstep)

/-- **The norm is surjective on every unit step above a prime-degree break.** For a Galois
extension of prime degree with an upper break at a natural number `t`, the norm maps
`U(L, ψℕ(v))` onto `U(K,v)` whenever `t < v`. -/
theorem map_normUnits_unitFiltration_after_break (hℓ : (Module.finrank K L).Prime)
    {t v : ℕ} (hvt : t < v)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v :=
  map_normUnits_unitFiltration_eq_of_surjective_normGradedMap v fun _ hn ↦
    (normGradedMap_after_break hℓ (hvt.trans_le hn) ht).surjective

/-- In a ramified Galois extension of prime degree, the last index `t` with `G_t ≠ 1` is a natural
upper break, and it lies below every depth `v` with `G_{ψℕ(v)} = 1`. -/
private theorem exists_lt_upperJump_of_finrank_prime (hℓ : (finrank K L).Prime) {v : ℕ}
    (hv : lowerRamificationGroup K L (psiNat K L v) = ⊥)
    (h0 : lowerRamificationGroup K L 0 ≠ ⊥) :
    ∃ t < v, UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  classical
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime := ⟨IsGalois.card_aut_eq_finrank K L ▸ hℓ⟩
  -- The break `t` is the least natural number with `G_{t+1} = 1`.
  have hex : ∃ n : ℕ, lowerRamificationGroup K L ((n + 1 : ℕ) : ℤ) = ⊥ := by
    refine ⟨psiNat K L v - 1, ?_⟩
    rcases Nat.eq_zero_or_pos (psiNat K L v) with h | h
    · exact absurd (by simpa [h] using hv) h0
    · rwa [Nat.sub_add_cancel h]
  set t := Nat.find hex
  have ht1 : lowerRamificationGroup K L ((t + 1 : ℕ) : ℤ) = ⊥ := Nat.find_spec hex
  have htne : lowerRamificationGroup K L t ≠ ⊥ := by
    rcases ht : t with _ | m
    · simpa using h0
    · exact Nat.find_min hex (by omega : m < t)
  have htop : lowerRamificationGroup K L t = ⊤ :=
    (lowerRamificationGroup K L t).eq_bot_or_eq_top_of_prime_card.resolve_left htne
  have hG0 : lowerRamificationGroup K L 0 = ⊤ :=
    top_le_iff.1 (htop ▸ lowerRamificationGroup_antitone K L (Int.natCast_nonneg t))
  have hψt : psiNat K L t = t := (psiNat_eq_self_iff K L).2 (htop.trans hG0.symm)
  have hlt : lowerRamificationGroup K L ((t : ℤ) + 1) < lowerRamificationGroup K L t := by
    rw [htop, ← Nat.cast_add_one, ht1]
    exact bot_lt_iff_ne_bot.2 (htop ▸ htne)
  have hlower : LowerJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
    simpa using (lowerJump_intCast_iff K L (i := t)
      (Nat.cast_mem_ramificationIndexDomain t)).2 hlt
  -- `ψ(t) = t`, so `φ(t) = t` and the lower break `t` is an upper break.
  have hinv : inverseHerbrand K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ =
      ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ :=
    Subtype.ext (by rw [← coe_psiNat, hψt])
  have hjump : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ :=
    ((congrArg (herbrand K L) hinv).symm.trans (herbrand_inverseHerbrand K L _)) ▸
      (upperJump_herbrand_iff K L _).2 hlower
  refine ⟨t, ?_, hjump⟩
  by_contra! hvt
  rw [psiNat_eq_self_of_le_break K L hℓ hvt hjump] at hv
  exact htne (eq_bot_iff.2 (hv ▸ lowerRamificationGroup_antitone K L (by exact_mod_cast hvt)))

/-- A trivial inertia group makes the extension unramified, so the norm is surjective at
all integral Herbrand depths. No prime-degree hypothesis is needed. -/
private theorem map_normUnits_unitFiltration_psiNat_eq_of_lowerRamificationGroup_zero_eq_bot
    (h0 : lowerRamificationGroup K L 0 = ⊥) (v : ℕ) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v := by
  have he : ramificationIndex K L = 1 := by
    rw [← natCard_lowerRamificationGroup_zero K L, h0, Subgroup.card_bot]
  have := (isUnramified_iff_ramificationIndex_eq_one (K := K) (L := L)).2 he
  rw [psiNat_of_isUnramified]
  exact map_normUnits_unitFiltration K L v

/-- In prime degree, the norm is surjective at every depth `v` at which the lower ramification
group `G_{ψℕ(v)}` is trivial: either `L/K` is unramified, or `v` lies above the break. -/
private theorem map_normUnits_unitFiltration_psiNat_eq_of_finrank_prime
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hv : lowerRamificationGroup K L (psiNat K L v) = ⊥) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v := by
  by_cases h0 : lowerRamificationGroup K L 0 = ⊥
  · exact map_normUnits_unitFiltration_psiNat_eq_of_lowerRamificationGroup_zero_eq_bot h0 v
  obtain ⟨t, htv, ht⟩ := exists_lt_upperJump_of_finrank_prime hℓ hv h0
  exact map_normUnits_unitFiltration_after_break hℓ htv ht

variable (K L) in
/-- Norm surjectivity at every natural depth `v` with `G^v = 1`, as a proposition about the
extension `L/K`; the induction on the degree runs through it. -/
private def NormSurj : Prop :=
  ∀ v : ℕ, upperRamificationGroup K L ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ = ⊥ →
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v

private theorem normSurj_of_finrank_prime (hℓ : (finrank K L).Prime) : NormSurj K L :=
  fun _ hv ↦ map_normUnits_unitFiltration_psiNat_eq_of_finrank_prime hℓ
    (by rwa [upperRamificationGroup_natCast] at hv)

/-- Norm surjectivity passes up a tower `L/F/K` in which `F/K` is Galois: `Gal(F/K)^v` is the
image of `G^v`, `Gal(L/F)^{ψℕ_{F/K}(v)}` is its trace on `Gal(L/F)`, and both the norm and the
integral inverse Herbrand function are transitive. -/
private theorem NormSurj.trans {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [Module.Finite K F]
    [IsGalois K F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L] [IsGalois F L]
    [IsScalarTower K F L] (hKF : NormSurj K F) (hFL : NormSurj F L) : NormSurj K L := by
  intro v hv
  have hF : upperRamificationGroup K F ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ = ⊥ := by
    rw [← map_restrictNormalHom_upperRamificationGroup K F L, hv, Subgroup.map_bot]
  have hL : upperRamificationGroup F L
      ⟨psiNat K F v, Nat.cast_mem_ramificationIndexDomain _⟩ = ⊥ := by
    have h := comap_restrictScalarsHom_upperRamificationGroup K F L
      ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩
    rw [hv, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).2
      (AlgEquiv.restrictScalarsHom_injective K)] at h
    convert h.symm using 2
    exact Subtype.ext (coe_psiNat K F v)
  have hnorm : (Algebra.normUnits K : Fˣ →* Kˣ).comp (Algebra.normUnits F : Lˣ →* Fˣ) =
      Algebra.normUnits K :=
    MonoidHom.ext fun y ↦ Units.ext (by simp [Algebra.norm_norm])
  rw [congrFun (psiNat_tower K F L) v, Function.comp_apply, ← hKF v hF, ← hFL _ hL,
    Subgroup.map_map, hnorm]

/-- The induction step: if norm surjectivity holds for `L` over every local field over which `L`
has smaller degree than over `K`, it holds for `L/K`. A trivial Galois group makes `L/K`
unramified; otherwise a normal subgroup of prime index gives a tower `L/F/K` with `F/K` Galois of
prime degree. -/
private theorem normSurj_of_forall_finrank_lt
    (ih : ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], finrank F L < finrank K L → NormSurj F L) :
    NormSurj K L := by
  rcases subsingleton_or_nontrivial (L ≃ₐ[K] L) with hG | hG
  · exact fun v _ ↦ map_normUnits_unitFiltration_psiNat_eq_of_lowerRamificationGroup_zero_eq_bot
      (Subgroup.eq_bot_of_subsingleton _) v
  · obtain ⟨F, hGalois, hp, hlt⟩ := exists_prime_degree_intermediateField K L
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    have := hGalois
    have := IsGalois.tower_top_of_isGalois K F L
    exact NormSurj.trans (normSurj_of_finrank_prime hp) (ih F hlt)

/-- Norm surjectivity for every finite Galois extension `L/F` with `F` in the universe of `L` and
`[L : F] ≤ d`, by induction on `d`. -/
private theorem normSurj_of_finrank_le (d : ℕ) :
    ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], finrank F L ≤ d → NormSurj F L :=
  finiteGaloisLocalField_induction_finrank_le L
    (fun F _ _ _ _ _ _ _ _ ↦ NormSurj F L)
    (fun F _ _ _ _ _ _ _ _ ↦ normSurj_of_forall_finrank_lt (K := F)) d

/-- **The norm is surjective above every upper break.** For a finite Galois extension `L/K` of
nonarchimedean local fields whose upper ramification group `G^v` is trivial at a natural number
`v`, the norm maps `U(L, ψℕ_{L/K}(v))` onto `U(K,v)`. -/
theorem map_normUnits_unitFiltration_psiNat_eq_of_upperRamificationGroup_eq_bot {v : ℕ}
    (hv : upperRamificationGroup K L ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ = ⊥) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v :=
  normSurj_of_forall_finrank_lt (fun F _ _ _ _ _ _ _ _ _ ↦ normSurj_of_finrank_le _ F le_rfl) v hv

end TauCeti
