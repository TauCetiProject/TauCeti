/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Conductor
import TauCeti.FieldTheory.Galois.Hilbert90
import TauCeti.GroupTheory.PGroup
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Norm.Equiv

/-!
# Hasse--Arf for cyclic extensions of prime-power degree

Let `L/K` be a finite Galois extension of nonarchimedean local fields whose Galois group `G` is
cyclic of order a power of a prime `p`. The **Hasse--Arf theorem** for `L/K` says that every
upper ramification break of `L/K` is an integer. This file proves it by induction on the degree,
comparing norms with the unit filtration.

Let `H` be the subgroup of order `p` of `G`, with fixed field `F`. The upper breaks of `L/K` are
those of `F/K`, integral by induction, together with `φ_{F/K}(t)` for the break `t` of the
prime-degree extension `L/F`. To see that `φ_{F/K}(t)` is an integer, suppose instead that
`ψℕ_{F/K}(n) < t < ψℕ_{F/K}(n + 1)`. For `x ∈ U(F,t)`, the Herbrand-shifted inclusion puts
`N_{F/K}(x)` in `U(K, n + 1)`, and `G^{n+1} = 1` makes `N_{F/K}` map `U(F, ψℕ_{F/K}(n + 1))`
onto `U(K, n + 1)`. So `x = w z` with `z ∈ U(F, t + 1)` and `N_{F/K}(w) = 1`, and by Hilbert's
Theorem 90 `w = g y / y` for a generator `g` of `Gal(F/K)`. Since `L/K` is Galois, `Gal(F/K)` acts
on the cokernel `U(F,0) / N_{L/F}(U(L,0))`, which has order `p`; being a `p`-group, it acts
trivially. A uniformizer of `F` is a norm from the totally ramified extension `L`, so `w` is a
norm from `L`. Hence every element of `U(F,t)` is a norm modulo `U(F, t + 1)`,
contradicting the fact that the graded norm of `L/F` at its break has cokernel of order `p`.

## Main results

* `TauCeti.LocalFieldsRamification.UpperJump.exists_psiNat_eq_of_isPGroup`: the induction step:
  in a tower `L/F/K` with `Gal(F/K)` a cyclic `ℓ`-group, `[L : F] = ℓ` prime, and no lower
  ramification of `F/K` beyond the break `t` of `L/F`, the break `t` is a value of `ψℕ_{F/K}`.
* `TauCeti.LocalFieldsRamification.UpperJump.exists_eq_intCast_of_isPGroup`: Hasse--Arf for
  cyclic extensions of prime-power degree.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, and Chapter V, §§3, 6 and 7.
-/

public section
noncomputable section

open Module TauCeti.LocalFieldsRamification

universe u v

namespace TauCeti.LocalFieldsRamification

section Tower

variable {K F L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K F] [ValuativeExtension K F] [Module.Finite K F] [IsGalois K F]
  [Algebra F L] [ValuativeExtension F L] [Module.Finite F L] [IsGalois F L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]
  [IsScalarTower K F L]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeExtension K F]
  [Module.Finite K F] [ValuativeExtension F L] [Module.Finite F L] [IsGalois F L] in
/-- The norms of integer units of `L` form a subgroup of `Fˣ` stable under `Aut(F/K)`. -/
private theorem smul_mem_map_normUnits (τ : F ≃ₐ[K] F) {y : Fˣ}
    (hy : y ∈ (unitFiltration L 0).map (Algebra.normUnits F)) :
    τ • y ∈ (unitFiltration L 0).map (Algebra.normUnits F) := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [← τ.restrict_liftNormal L, AlgEquiv.restrictNormal_smul_normUnits]
  exact Subgroup.mem_map_of_mem _ (by
    simpa only [AlgEquiv.smul_units_def] using
      (AlgEquiv.unitsMap_mem_unitFiltration_iff (τ.liftNormal L)).2 hz)

/-- In prime degree `ℓ` with an upper break, an automorphism of `F/K` of `ℓ`-power order moves
every unit of `𝒪[F]` by a norm of a unit of `𝒪[L]`: it acts on the quotient of `U(F,0)` by these
norms, a group of order `ℓ`, and so acts trivially. -/
private theorem smul_div_mem_map_normUnits_of_mem_unitFiltration_zero
    (hℓ : (finrank F L).Prime) {t : ℕ}
    (ht : UpperJump F L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩)
    {σ : F ≃ₐ[K] F} {k : ℕ} (hσ : σ ^ finrank F L ^ k = 1) {y : Fˣ}
    (hy : y ∈ unitFiltration F 0) :
    σ • y / y ∈ (unitFiltration L 0).map (Algebra.normUnits F) := by
  have : Fact (finrank F L).Prime := ⟨hℓ⟩
  set N := (unitFiltration L 0).map (Algebra.normUnits F)
  set U := unitFiltration F 0
  let N' := N.subgroupOf U
  have hcard : Nat.card (U ⧸ N') = finrank F L := by
    rw [← Subgroup.index_eq_card, ← relIndex_normUnits_unitFiltration_zero hℓ ht,
      Subgroup.relIndex]
  let φ := MulDistribMulAction.toMonoidHom U σ
  have hφ : N' ≤ N'.comap φ := fun u hu ↦ Subgroup.mem_comap.2 <|
    Subgroup.mem_subgroupOf.2 (smul_mem_map_normUnits σ (Subgroup.mem_subgroupOf.1 hu))
  let f := QuotientGroup.map N' N' φ hφ
  have hiter (n : ℕ) (u : U) : f^[n] (u : U ⧸ N') = ((σ ^ n • u : U) : U ⧸ N') := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, QuotientGroup.map_mk,
        MulDistribMulAction.toMonoidHom_apply, pow_succ', mul_smul]
  have hfix := f.apply_eq_self_of_iterate_pow_eq_self hcard (k := k)
    (fun a ↦ QuotientGroup.induction_on a fun u ↦ by rw [hiter, hσ, one_smul])
    (⟨y, hy⟩ : U)
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hfix.symm)
  rwa [div_eq_inv_mul]

/-- In prime degree `ℓ` with an upper break, an automorphism of `F/K` of `ℓ`-power order moves
every element of `Fˣ` by a norm of a unit of `𝒪[L]`. On units this is the triviality of the
action on the norm cokernel; a uniformizer of `F` is the norm of one of `L`, because `L/F` is
totally ramified. -/
private theorem smul_div_mem_map_normUnits
    (hℓ : (finrank F L).Prime) {t : ℕ}
    (ht : UpperJump F L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩)
    {σ : F ≃ₐ[K] F} {k : ℕ} (hσ : σ ^ finrank F L ^ k = 1) (y : Fˣ) :
    σ • y / y ∈ (unitFiltration L 0).map (Algebra.normUnits F) := by
  set N := (unitFiltration L 0).map (Algebra.normUnits F)
  -- `y ↦ σ y / y` is a homomorphism of the commutative group `Fˣ`.
  let c : Fˣ →* Fˣ := MulDistribMulAction.toMonoidHom Fˣ σ / MonoidHom.id Fˣ
  have hc (x : Fˣ) : c x = σ • x / x := by
    rw [MonoidHom.div_apply, MulDistribMulAction.toMonoidHom_apply, MonoidHom.id_apply]
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer (K := L)
  have htot : IsTotallyRamified F L := (lowerRamificationGroup_zero_eq_top_iff F L).1 <|
    top_le_iff.1 (lowerRamificationGroup_natCast_eq_top_of_upperJump F L hℓ ht ▸
      lowerRamificationGroup_antitone F L (Int.natCast_nonneg t))
  have hπ : IsUniformizer F (Algebra.normUnits F ϖ) :=
    (isUniformizer_normUnits_iff hϖ).2 htot.inertiaDegree_eq_one
  have hπN : c (Algebra.normUnits F ϖ) ∈ N := by
    rw [hc, ← σ.restrict_liftNormal L, AlgEquiv.restrictNormal_smul_normUnits, ← map_div]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← ker_normalizedValuation, MonoidHom.mem_ker, map_div, AlgEquiv.smul_units_def,
      AlgEquiv.normalizedValuation_unitsMap, div_self']
  set n := (normalizedValuation F y).toAdd
  have hu := mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def _).1 hπ) y
  have hy : c y = c (y * Algebra.normUnits F ϖ ^ (-n)) * c (Algebra.normUnits F ϖ) ^ n := by
    rw [← map_zpow c, ← map_mul c, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [← hc, hy]
  exact mul_mem (smul_div_mem_map_normUnits_of_mem_unitFiltration_zero hℓ ht hσ hu)
    (zpow_mem hπN n)

/-- **The induction step of Hasse--Arf.** Let `L/F/K` be a tower of Galois extensions of
nonarchimedean local fields in which `L/F` has prime degree `ℓ` with an upper break at the natural
number `t`, and `Gal(F/K)` is a cyclic `ℓ`-group with trivial lower ramification group
`Gal(F/K)_{t+1}`. Then `t = ψℕ_{F/K}(n)` for some natural number `n`; equivalently, the Herbrand
function `φ_{F/K}` takes the break `t` to an integer. -/
theorem UpperJump.exists_psiNat_eq_of_isPGroup [IsCyclic (F ≃ₐ[K] F)]
    {t : ℕ} (ht : UpperJump F L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩)
    (hℓ : (finrank F L).Prime) (hp : IsPGroup (finrank F L) (F ≃ₐ[K] F))
    (hbot : lowerRamificationGroup K F (t + 1 : ℕ) = ⊥) :
    ∃ n, psiNat K F n = t := by
  classical
  by_contra! hne
  -- `t` lies strictly between two consecutive values `ψℕ(n) < t < ψℕ(n + 1)`.
  have hex : ∃ n, t < psiNat K F (n + 1) := ⟨t, t.lt_succ_self.trans_le (self_le_psiNat K F _)⟩
  set n := Nat.find hex
  have hn1 : t < psiNat K F (n + 1) := Nat.find_spec hex
  have hn0 : psiNat K F n < t := by
    refine lt_of_le_of_ne ?_ (hne n)
    rcases hn : n with _ | m
    · simp
    · exact not_lt.1 (Nat.find_min hex (by omega : m < n))
  -- Every unit of depth `t` is a norm from `U(L, ψℕ_{L/F}(t))` modulo `U(F, t + 1)`.
  have hle : unitFiltration F t ≤
      (unitFiltration L (psiNat F L t)).map (Algebra.normUnits F) ⊔ unitFiltration F (t + 1) := by
    intro x hx
    have hxN : Algebra.normUnits K x ∈ unitFiltration K (n + 1) :=
      map_normUnits_unitFiltration_psiNat_add_one_le K F n
        (Subgroup.mem_map_of_mem _ (unitFiltration_antitone hn0 hx))
    have hsurj := map_normUnits_unitFiltration_psiNat_eq_of_upperRamificationGroup_eq_bot
      (K := K) (L := F) (v := n + 1) <| by
        rw [upperRamificationGroup_natCast]
        exact eq_bot_iff.2 (hbot ▸ lowerRamificationGroup_antitone K F (by exact_mod_cast hn1))
    rw [← hsurj] at hxN
    obtain ⟨z, hz, hzx⟩ := hxN
    have hz' : z ∈ unitFiltration F (t + 1) := unitFiltration_antitone hn1 hz
    -- `w = x z⁻¹` has norm one, so it is `g y / y` by Hilbert's Theorem 90.
    set w := x * z⁻¹
    have hw : w ∈ unitFiltration F t :=
      mul_mem hx (inv_mem (unitFiltration_antitone t.le_succ hz'))
    have hNw : Algebra.norm K ((w : Fˣ) : F) = 1 := by
      have h : Algebra.normUnits K w = 1 := by rw [map_mul, map_inv, hzx, mul_inv_cancel]
      simpa only [Algebra.coe_normUnits, Units.val_one] using congrArg Units.val h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F ≃ₐ[K] F)
    obtain ⟨y, hy⟩ := exists_smul_div_eq_of_norm_eq_one hg hNw
    obtain ⟨k, hk⟩ := hp g
    have hwN : w ∈ (unitFiltration L 0).map (Algebra.normUnits F) := by
      rw [← hy]
      exact smul_div_mem_map_normUnits hℓ ht hk y
    have hwt : w ∈ (unitFiltration L (psiNat F L t)).map (Algebra.normUnits F) := by
      rw [← map_normUnits_unitFiltration_zero_inf_of_le_break hℓ le_rfl ht]
      exact ⟨hwN, hw⟩
    have hwz : w * z = x := inv_mul_cancel_right x z
    rw [← hwz]
    exact Subgroup.mul_mem_sup hwt hz'
  have hone := Subgroup.relIndex_eq_one.2 hle
  rw [relIndex_normUnits_unitFiltration_sup_at_break hℓ ht] at hone
  exact hℓ.ne_one hone

/-- In a tower `L/F/K` with `Gal(L/K)` a cyclic `p`-group and `L/F` of prime degree with upper
break `t`, the lower ramification group `Gal(F/K)_{t+1}` is trivial. It is the image of
`G^w` for `w = φ_{F/K}(t + 1)`, whose trace `Gal(L/F)^{t+1}` on `Gal(L/F)` is trivial; the subgroups
of a cyclic `p`-group form a chain, so `G^w` itself is trivial. -/
private theorem lowerRamificationGroup_add_one_eq_bot_of_isPGroup [IsCyclic (L ≃ₐ[K] L)] {p : ℕ}
    [Fact p.Prime] (hp : IsPGroup p (L ≃ₐ[K] L)) (hℓ : (finrank F L).Prime) {t : ℕ}
    (ht : UpperJump F L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K F (t + 1 : ℕ) = ⊥ := by
  set w := herbrand K F ⟨(t + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain _⟩
  have hcomap : (upperRamificationGroup K L w).comap
      (AlgEquiv.restrictScalarsHom (S := F) K) = ⊥ := by
    rw [comap_restrictScalarsHom_upperRamificationGroup K F L, inverseHerbrand_herbrand,
      upperRamificationGroup_natCast]
    exact eq_bot_iff.2 (lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump F L hℓ ht ▸
      lowerRamificationGroup_antitone F L (by exact_mod_cast self_le_psiNat F L (t + 1)))
  have hGw : upperRamificationGroup K L w = ⊥ := by
    rcases hp.le_total_of_isCyclic (upperRamificationGroup K L w)
        (AlgEquiv.restrictScalarsHom (S := F) K).range with h | h
    · rw [← Subgroup.map_comap_eq_self h, hcomap, Subgroup.map_bot]
    · -- Otherwise `Gal(L/F)` would be trivial, contradicting `[L : F] > 1`.
      have : Nontrivial (L ≃ₐ[F] L) := Finite.one_lt_card_iff_nontrivial.1 <| by
        rw [IsGalois.card_aut_eq_finrank]
        exact hℓ.one_lt
      refine absurd (eq_top_iff.2 fun σ _ ↦ h ⟨σ, rfl⟩ : (upperRamificationGroup K L w).comap
        (AlgEquiv.restrictScalarsHom (S := F) K) = ⊤) ?_
      rw [hcomap]
      exact bot_ne_top
  have hlow : lowerRamificationGroup K F (t + 1 : ℕ) = upperRamificationGroup K F w := by
    rw [upperRamificationGroup_herbrand, ← lowerRamificationGroupReal_intCast, Int.cast_natCast]
  rw [hlow, ← map_restrictNormalHom_upperRamificationGroup K F L, hGw, Subgroup.map_bot]

end Tower

section Cyclic

variable {K : Type u} {L : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

variable (K) in
/-- Hasse--Arf for the cyclic `p`-extensions of `K` of degree less than `[L : K]` in the universe of
`L`, as a hypothesis for the induction on the degree. -/
private def HasseArfBelow (p : ℕ) (d : ℕ) : Prop :=
  ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra K F] [ValuativeExtension K F] [Module.Finite K F] [IsGalois K F]
    [IsCyclic (F ≃ₐ[K] F)], IsPGroup p (F ≃ₐ[K] F) → finrank K F < d →
    ∀ u : RamificationIndexDomain, UpperJump K F u → ∃ z : ℤ, (u : ℝ) = z

/-- The induction step for Hasse--Arf in a cyclic `p`-extension `L/K`: the fixed field `F` of the
subgroup of order `p` has integral upper breaks by induction, and the remaining break is
`φ_{F/K}(t)` for the break `t` of `L/F`, integral by
`UpperJump.exists_psiNat_eq_of_isPGroup`. -/
private theorem UpperJump.exists_eq_intCast_of_hasseArfBelow [IsCyclic (L ≃ₐ[K] L)] {p : ℕ}
    [hp' : Fact p.Prime] (hp : IsPGroup p (L ≃ₐ[K] L)) (ih : HasseArfBelow.{u, v} K p (finrank K L))
    {u : RamificationIndexDomain} (hu : UpperJump K L u) : ∃ z : ℤ, (u : ℝ) = z := by
  have := hu.nontrivial K L
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := L ≃ₐ[K] L) p
    ((hp.card_eq_or_dvd).resolve_left Finite.one_lt_card.ne')
  let H := Subgroup.zpowers h
  let F := IntermediateField.fixedField H
  let _ := finiteIntermediateFieldValuativeRel K L F
  let _ := finiteIntermediateFieldTopology K L F
  have := finiteIntermediateField_isNonarchimedeanLocalField K L F
  have := finiteIntermediateField_valuativeExtension K L F
  have := IsGalois.tower_top_of_isGalois K F L
  have hFL : finrank F L = p := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hh]
  have hlt : finrank K F < finrank K L := by
    rw [← Module.finrank_mul_finrank K F L, hFL]
    have := hp'.out.two_le
    have := Module.finrank_pos (R := K) (M := F)
    nlinarith
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) L
  have : IsCyclic (F ≃ₐ[K] F) := isCyclic_of_surjective _ hsurj
  have hpF : IsPGroup p (F ≃ₐ[K] F) := hp.of_surjective _ hsurj
  rcases (upperJump_iff_upperJump_or_upperJump_inverseHerbrand K F L u).1 hu with hKF | hFL'
  · exact ih F hpF hlt u hKF
  have hℓ : (finrank F L).Prime := hFL ▸ hp'.out
  rcases hFL'.eq_neg_one_or_exists_eq_natCast_of_finrank_prime hℓ with hneg | ⟨t, ht⟩
  · -- `ψ_{F/K}(u) = -1` forces `u = -1`.
    refine ⟨-1, ?_⟩
    have hψ : inverseHerbrand K F u = ⟨-1, le_rfl⟩ := Subtype.ext hneg
    rw [← herbrand_inverseHerbrand K F u, hψ, herbrand_of_coe_le_zero K F (by norm_num)]
    norm_num
  · have hψt : inverseHerbrand K F u = ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ :=
      Subtype.ext ht
    have ht' : UpperJump F L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := hψt ▸ hFL'
    obtain ⟨n, hn⟩ := ht'.exists_psiNat_eq_of_isPGroup hℓ (hFL ▸ hpF)
      (lowerRamificationGroup_add_one_eq_bot_of_isPGroup hp hℓ ht')
    refine ⟨n, ?_⟩
    -- `ψ_{F/K}(u) = t = ψ_{F/K}(n)`, so `u = n`.
    have hψ : inverseHerbrand K F u =
        inverseHerbrand K F ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ :=
      Subtype.ext (by rw [ht, ← hn, coe_psiNat])
    rw [← herbrand_inverseHerbrand K F u, hψ, herbrand_inverseHerbrand]
    simp

variable (K) in
private theorem hasseArfBelow (p : ℕ) [Fact p.Prime] (d : ℕ) : HasseArfBelow.{u, v} K p d := by
  induction d with
  | zero => exact fun F _ _ _ _ _ _ _ _ _ _ h ↦ absurd h (Nat.not_lt_zero _)
  | succ d ih =>
    intro F _ _ _ _ _ _ _ _ _ hp hd u hu
    exact hu.exists_eq_intCast_of_hasseArfBelow hp fun F' _ _ _ _ _ _ _ _ _ hp' h' ↦
      ih F' hp' (by omega)

/-- **Hasse--Arf for cyclic extensions of prime-power degree.** If the Galois group of a finite
Galois extension `L/K` of nonarchimedean local fields is cyclic of `p`-power order, every upper
ramification break of `L/K` is an integer. -/
theorem UpperJump.exists_eq_intCast_of_isPGroup [IsCyclic (L ≃ₐ[K] L)] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p (L ≃ₐ[K] L)) {u : RamificationIndexDomain} (hu : UpperJump K L u) :
    ∃ z : ℤ, (u : ℝ) = z :=
  hu.exists_eq_intCast_of_hasseArfBelow hp (hasseArfBelow K p _)

end Cyclic

end TauCeti.LocalFieldsRamification
