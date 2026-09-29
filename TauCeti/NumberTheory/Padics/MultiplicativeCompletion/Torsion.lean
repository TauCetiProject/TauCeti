/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
public import TauCeti.NumberTheory.LocalField.RootsOfUnity

/-!
# Torsion in the p-adic completion of a multiplicative group

For a prime `p` and a field `L`, this file computes the torsion of the completed multiplicative
module `A(L) = lim_m Lˣ/(Lˣ)^(p^m)` of `TauCeti.padicCompletionUnits`: it is exactly the image
of the `p`-power roots of unity of `L`. Every level `Lˣ/(Lˣ)^(p^m)` has exponent dividing `p^m`,
so `A(L)` has no torsion prime to `p`; an element killed by `p^j` is, at every level, the class of
a `p^j`-th root of unity, and since there are only finitely many of those a single root of unity
represents it at all levels simultaneously.

When the `p`-power roots of unity of `L` are finite (for instance when `L` is a finite extension
of `ℚ_p`, by `TauCeti.finite_pPowerRootsOfUnity`), they embed into `A(L)`, so the torsion of
`A(L)` is finite of order `q(L) = TauCeti.localRootOfUnityOrder`. Finally, the torsion of `A(L)`
as a `ℤ_p`-module is the torsion of the underlying multiplicative group: being killed by a nonzero
`p`-adic integer is being killed by a power of `p`.

## Main results

* `TauCeti.padicCompletionUnits_pow_eq_one_iff`: an element of `A(L)` is killed by `p^j` exactly
  when it is the class of a `p^j`-th root of unity.
* `TauCeti.torsion_padicCompletionUnits`: the torsion subgroup of `A(L)` is the image of
  `TauCeti.pPowerRootsOfUnity p L`.
* `TauCeti.padicCompletionUnitsOf_injOn_pPowerRootsOfUnity`: finitely many `p`-power roots of
  unity embed into `A(L)`.
* `TauCeti.natCard_torsion_padicCompletionUnits`: the torsion of `A(L)` has order `q(L)`.
* `TauCeti.mem_torsion_padicCompletionUnits_iff`: the `ℤ_p`-torsion submodule of `A(L)` is the
  additive form of its group torsion.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.4.
-/

public section

namespace TauCeti

variable (p : ℕ) (L : Type*) [Field L]

/-- A representative of one coordinate of a compatible family represents every lower
coordinate. -/
private theorem mk_eq_padicCompletionUnits_apply_of_le (x : ↑(padicCompletionUnits p L))
    {k l : ℕ} (hkl : k ≤ l) {u : Lˣ}
    (hu : (u : Lˣ ⧸ (powMonoidHom (p ^ l) : Lˣ →* Lˣ).range) = x.1 l) :
    (u : Lˣ ⧸ (powMonoidHom (p ^ k) : Lˣ →* Lˣ).range) = x.1 k := by
  induction l, hkl using Nat.le_induction with
  | base => exact hu
  | succ l _ ih =>
    apply ih
    rw [← padicCompletionTransition_mk p L l u, hu]
    exact (mem_padicCompletionUnits_iff p L x.1).mp x.2 l

/-- An element of `A(L)` killed by a natural number prime to `p` is trivial. -/
private theorem eq_one_of_pow_eq_one_of_coprime (x : ↑(padicCompletionUnits p L)) {n : ℕ}
    (hn : n.Coprime p) (hx : x ^ n = 1) : x = 1 := by
  apply Subtype.ext
  funext m
  have hxm : x.1 m ^ n = 1 := by
    simpa using congrArg (fun y : ↑(padicCompletionUnits p L) ↦ y.1 m) hx
  exact (pow_eq_one_iff_of_coprime (hn.pow_right m)).mp
    ⟨hxm, QuotientGroup.pow_eq_one_quotient_range_powMonoidHom _ _⟩

variable [Fact p.Prime]

/-- An element of `A(L)` is killed by `p^j` exactly when it is the class of a `p^j`-th root of
unity of `L`. -/
theorem padicCompletionUnits_pow_eq_one_iff (x : ↑(padicCompletionUnits p L)) (j : ℕ) :
    x ^ p ^ j = 1 ↔ x ∈ (rootsOfUnity (p ^ j) L).map (padicCompletionUnitsOf p L) := by
  constructor
  · intro hx
    -- At every level `m`, the coordinate `x_m` is the class of a `p^j`-th root of unity.
    have hlevel : ∀ m, ∃ ζ : rootsOfUnity (p ^ j) L,
        ((ζ : Lˣ) : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) = x.1 m := by
      intro m
      obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x.1 (m + j))
      have hpow :
          ((u ^ p ^ j : Lˣ) : Lˣ ⧸ (powMonoidHom (p ^ (m + j)) : Lˣ →* Lˣ).range) = 1 := by
        rw [QuotientGroup.mk_pow, hu]
        simpa using congrArg (fun y : ↑(padicCompletionUnits p L) ↦ y.1 (m + j)) hx
      obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp hpow
      rw [powMonoidHom_apply] at hv
      refine ⟨⟨u * (v ^ p ^ m)⁻¹, ?_⟩, ?_⟩
      · rw [mem_rootsOfUnity, mul_pow, inv_pow, ← pow_mul, ← pow_add, hv, mul_inv_cancel]
      · have hv1 : ((v ^ p ^ m : Lˣ) : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr ⟨v, rfl⟩
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hv1, inv_one, mul_one]
        exact mk_eq_padicCompletionUnits_apply_of_le p L x (Nat.le_add_right m j) hu
    -- Finitely many roots of unity serve infinitely many levels, so one of them serves
    -- arbitrarily high levels, hence every level.
    choose ζ hζ using hlevel
    obtain ⟨ξ, hξ⟩ := Finite.exists_infinite_fiber ζ
    refine ⟨ξ, ξ.2, Subtype.ext (funext fun m ↦ ?_)⟩
    obtain ⟨l, hl, hml⟩ := (Set.infinite_coe_iff.mp hξ).exists_gt m
    rw [padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply]
    refine mk_eq_padicCompletionUnits_apply_of_le p L x hml.le ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hl
    rw [← hl]
    exact hζ l
  · rintro ⟨ζ, hζ, rfl⟩
    rw [← map_pow, (mem_rootsOfUnity _ _).mp hζ, map_one]

/-- The torsion subgroup of `A(L)` is the image of the `p`-power roots of unity of `L`. -/
theorem torsion_padicCompletionUnits :
    CommGroup.torsion ↑(padicCompletionUnits p L) =
      (pPowerRootsOfUnity p L).map (padicCompletionUnitsOf p L) := by
  have hp : p.Prime := Fact.out
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
    have hxa : x ^ p ^ a = 1 :=
      eq_one_of_pow_eq_one_of_coprime p L _ ((hp.coprime_iff_not_dvd.mpr hb).symm)
        (by rw [← pow_mul, hxn])
    obtain ⟨ζ, hζ, rfl⟩ := (padicCompletionUnits_pow_eq_one_iff p L x a).mp hxa
    exact ⟨ζ, (mem_pPowerRootsOfUnity_iff p L ζ).mpr ⟨a, (mem_rootsOfUnity _ _).mp hζ⟩, rfl⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    obtain ⟨a, ha⟩ := (mem_pPowerRootsOfUnity_iff p L ζ).mp hζ
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p ^ a, pow_pos hp.pos a, by rw [← map_pow, ha, map_one]⟩

/-- When `L` has only finitely many `p`-power roots of unity, they map injectively to `A(L)`:
a `p`-power root of unity that is a `p^m`-th power for every `m` is trivial. -/
theorem padicCompletionUnitsOf_injOn_pPowerRootsOfUnity (h : Finite (pPowerRootsOfUnity p L)) :
    Set.InjOn (padicCompletionUnitsOf p L) (pPowerRootsOfUnity p L) := by
  intro ζ hζ ξ hξ he
  obtain ⟨k, hk⟩ := localRootOfUnityOrder_isPow p L h
  have hη : ((ζ * ξ⁻¹ : Lˣ) : Lˣ ⧸ (powMonoidHom (p ^ k) : Lˣ →* Lˣ).range) = 1 := by
    have hof : padicCompletionUnitsOf p L (ζ * ξ⁻¹) = 1 := by
      rw [map_mul, map_inv, he, mul_inv_cancel]
    simpa using congrArg (fun y : ↑(padicCompletionUnits p L) ↦ y.1 k) hof
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp hη
  rw [powMonoidHom_apply] at hv
  have hvT : v ∈ pPowerRootsOfUnity p L := by
    obtain ⟨a, ha⟩ := (mem_pPowerRootsOfUnity_iff p L _).mp (mul_mem hζ (inv_mem hξ))
    exact (mem_pPowerRootsOfUnity_iff p L v).mpr ⟨k + a, by rw [pow_add, pow_mul, hv, ha]⟩
  rw [pPowerRootsOfUnity_eq_rootsOfUnity_order p L h, hk, mem_rootsOfUnity] at hvT
  rw [hvT] at hv
  exact mul_inv_eq_one.mp hv.symm

/-- When `L` has only finitely many `p`-power roots of unity, the torsion of `A(L)` has order
`q(L)`, the order of the group of `p`-power roots of unity of `L`. -/
theorem natCard_torsion_padicCompletionUnits (h : Finite (pPowerRootsOfUnity p L)) :
    Nat.card (CommGroup.torsion ↑(padicCompletionUnits p L)) = localRootOfUnityOrder p L h := by
  rw [torsion_padicCompletionUnits, localRootOfUnityOrder_def, ← SetLike.coe_sort_coe,
    Subgroup.coe_map,
    Nat.card_image_of_injOn (padicCompletionUnitsOf_injOn_pPowerRootsOfUnity p L h),
    SetLike.coe_sort_coe]

/-- When `L` has only finitely many `p`-power roots of unity, the torsion of `A(L)` is finite. -/
theorem finite_torsion_padicCompletionUnits (h : Finite (pPowerRootsOfUnity p L)) :
    Finite (CommGroup.torsion ↑(padicCompletionUnits p L)) :=
  Nat.finite_of_card_ne_zero <| by
    rw [natCard_torsion_padicCompletionUnits p L h]
    exact (localRootOfUnityOrder_pos p L h).ne'

/-- The `ℤ_p`-torsion submodule of `A(L)` is the additive form of its group torsion: an element
is killed by a nonzero `p`-adic integer exactly when it has finite multiplicative order. -/
theorem mem_torsion_padicCompletionUnits_iff (x : Additive ↑(padicCompletionUnits p L)) :
    x ∈ Submodule.torsion ℤ_[p] (Additive ↑(padicCompletionUnits p L)) ↔
      x.toMul ∈ CommGroup.torsion ↑(padicCompletionUnits p L) := by
  have hp : p.Prime := Fact.out
  rw [Submodule.mem_torsion_iff, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    -- Dividing by the unit part of `a` leaves a power of `p` that kills `x`.
    have hpx : (p ^ a.valuation : ℕ) • x = 0 := by
      have hu : (((PadicInt.unitCoeff ha0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * a =
          (p : ℤ_[p]) ^ a.valuation := by
        conv_lhs => arg 2; rw [PadicInt.unitCoeff_spec ha0]
        rw [← mul_assoc, Units.inv_mul, one_mul]
      rw [← padicCompletionUnits_natCast_smul, Nat.cast_pow, ← hu, mul_smul,
        ← Submonoid.smul_def ⟨a, ha⟩, hax, smul_zero]
    refine ⟨p ^ a.valuation, pow_pos hp.pos _, ?_⟩
    rw [← toMul_nsmul, hpx, toMul_zero]
  · rintro ⟨n, hn, hxn⟩
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')⟩, ?_⟩
    rw [Submonoid.smul_def, padicCompletionUnits_natCast_smul]
    apply Additive.toMul.injective
    rw [toMul_nsmul, hxn, toMul_zero]

end TauCeti
