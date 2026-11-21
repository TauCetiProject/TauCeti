/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Ramification and inertia over local rings and discrete valuation rings

Let `S → T` be a local homomorphism from a local ring to a discrete valuation ring such that the
maximal ideal `𝔪_S` of `S` does not map to zero. Then `𝔪_S T` is a nonzero ideal of `T`, hence a
power `𝔪_T ^ e` of the maximal ideal of `T`, and `e` is Mathlib's ramification index
`(maximalIdeal T).ramificationIdx S`, the length of `T ⧸ 𝔪_S T`. For an extension of discrete
valuation rings this is the ramification index of Stacks, Definition 15.113.1 (09E4): the
exponent `e` with `π_S = u π_T ^ e` for uniformizers `π_S`, `π_T` and a unit `u`.

## Main results

* `TauCeti.IsLocalRing.inertiaDeg_maximalIdeal`:
  `(maximalIdeal B).inertiaDeg A = Module.finrank (ResidueField A) (ResidueField B)`.
* `TauCeti.IsDiscreteValuationRing.asIdeal_maximalIdeal` and `maximalIdeal_liesOver`: bridge from
  `IsDiscreteValuationRing.maximalIdeal` to `IsLocalRing.maximalIdeal`.
* `TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with
  `e` the ramification index of `𝔪_T` over `S`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow`: the index equals
  any exponent satisfying this maximal-ideal identity.
* `TauCeti.IsDiscreteValuationRing.exists_unit_mul_pow_ramificationIdx`: for a local homomorphism
  of discrete valuation rings sending a uniformizer `π` to a nonzero element, `π` maps to a unit
  times `ϖ ^ e` for any uniformizer `ϖ` of the target.
* `TauCeti.IsDiscreteValuationRing.exists_unit_mul_pow_ramificationIdx_localization`: localization
  version at a prime `P` of an `A`-algebra `C` lying over `𝔪_A` whose localization is a discrete
  valuation ring in which `π` does not vanish.
* `TauCeti.IsDiscreteValuationRing.addVal_algebraMap`: for an extension of discrete valuation
  rings, `v_T = e · v_S` on `S`.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`:
  `map_maximalIdeal_eq_pow_ramificationIdx` is the local form of its
  `Pcf.heightOneRamificationIdx_eq_dvrExponent` with `Pcf.heightOneDvrExponent_spec`, stated
  there at a height-one prime of a finite extension of normal Noetherian domains.
-/

public section

open IsLocalRing
open IsDiscreteValuationRing hiding maximalIdeal

namespace TauCeti.IsLocalRing

/-- For a local homomorphism `A → B` of local rings, `(maximalIdeal B).inertiaDeg A` equals the
residue-field extension degree. -/
theorem inertiaDeg_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    (maximalIdeal B).inertiaDeg A = Module.finrank (ResidueField A) (ResidueField B) := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) (maximalIdeal B)]
  -- `ResidueField R` is defined as `R ⧸ maximalIdeal R` and its `Algebra` structure is
  -- `Ideal.Quotient.algebraOfLiesOver`, so `RingEquiv.refl` identifies both sides definitionally.
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (ResidueField A))
    (RingEquiv.refl (ResidueField B)) (RingHom.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)

end TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

/-- The underlying ideal of `IsDiscreteValuationRing.maximalIdeal A` is `maximalIdeal A`. -/
theorem asIdeal_maximalIdeal (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    (_root_.IsDiscreteValuationRing.maximalIdeal A).asIdeal = maximalIdeal A := rfl

/-- For a local homomorphism of DVRs, the height-one maximal ideal of `B` lies over that of `A`. -/
instance maximalIdeal_liesOver {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    (_root_.IsDiscreteValuationRing.maximalIdeal B).asIdeal.LiesOver
      (_root_.IsDiscreteValuationRing.maximalIdeal A).asIdeal := by
  rw [asIdeal_maximalIdeal, asIdeal_maximalIdeal]
  infer_instance

section

variable {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S] [IsDomain T]
  [_root_.IsDiscreteValuationRing T] [Algebra S T] [IsLocalHom (algebraMap S T)]

/-- For a local homomorphism from a local ring `S` to a discrete valuation ring `T` under which
the maximal ideal of `S` does not vanish, `𝔪_S T = 𝔪_T ^ e` with `e` the ramification index of the
maximal ideal of `T` over `S`. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx
    (h : (maximalIdeal S).map (algebraMap S T) ≠ ⊥) :
    (maximalIdeal S).map (algebraMap S T) =
      maximalIdeal T ^ (maximalIdeal T).ramificationIdx S := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible h hϖ
  have hpow : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  -- The length-based ramification index agrees with the exponent-based one over the Dedekind
  -- domain `T` (`Ideal.ramificationIdx'_eq_ramificationIdx'`), and the latter is `n`.
  have : (maximalIdeal T).LiesOver (maximalIdeal S) :=
    ⟨(maximalIdeal_comap (algebraMap S T)).symm⟩
  have hidx : (maximalIdeal T).ramificationIdx S = n := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (maximalIdeal S) (maximalIdeal T) h]
    refine Ideal.ramificationIdx'_spec hpow.le ?_
    rw [hpow]
    exact (Ideal.pow_succ_lt_pow (not_a_field T) n).not_ge
  rw [hidx, hpow]

/-- For a local homomorphism to a DVR, the exponent in a maximal-ideal power identity is the
ramification index. This is the exponent characterization of Stacks, Definition 15.113.1 (09E4),
with no DVR assumption on the base ring. -/
@[stacks 09E4 "exponent characterization with arbitrary local base ring"]
theorem ramificationIdx_eq_of_map_maximalIdeal_eq_pow {exponent : ℕ}
    (hexponent : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ exponent) :
    (maximalIdeal T).ramificationIdx S = exponent := by
  have hpowers : StrictAnti (fun power : ℕ ↦ maximalIdeal T ^ power) :=
    Ideal.pow_right_strictAnti (maximalIdeal T) (not_a_field T) (maximalIdeal.isMaximal T).ne_top
  have hmap : (maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    rw [hexponent]
    exact ne_of_gt (lt_of_le_of_lt bot_le (hpowers (Nat.lt_succ_self exponent)))
  exact hpowers.injective ((map_maximalIdeal_eq_pow_ramificationIdx hmap).symm.trans hexponent)

/-- For a local homomorphism `A → B` of discrete valuation rings with uniformizers `π` and `ϖ`
such that `algebraMap A B π ≠ 0`, the image of `π` in `B` is a unit times
`ϖ ^ (maximalIdeal B).ramificationIdx A`. -/
theorem exists_unit_mul_pow_ramificationIdx {A B : Type*} [CommRing A] [IsDomain A]
    [_root_.IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    {π : A} (hπ : Irreducible π) (hπB : algebraMap A B π ≠ 0)
    {ϖ : B} (hϖ : Irreducible ϖ) :
    ∃ u : Bˣ, algebraMap A B π = ↑u * ϖ ^ (maximalIdeal B).ramificationIdx A := by
  have hmap_ne : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := fun hbot ↦
    hπB (Ideal.mem_bot.mp
      (hbot ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).mpr hπ.not_isUnit)))
  have hmap := map_maximalIdeal_eq_pow_ramificationIdx hmap_ne
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmap
  nth_rw 1 [hϖ.maximalIdeal_eq] at hmap
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hmap
  obtain ⟨u, hu⟩ := hmap.symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- For a discrete valuation ring `A` with uniformizer `π` and a prime `P` of an `A`-algebra `C`
lying over `maximalIdeal A` whose localization is a discrete valuation ring with uniformizer `ϖ`
in which `π` does not vanish, the image of `π` in `Localization.AtPrime P` is a unit times
`ϖ ^ P.ramificationIdx A`. -/
theorem exists_unit_mul_pow_ramificationIdx_localization
    {A C : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
    [CommRing C] [Algebra A C]
    {π : A} (hπ : Irreducible π) (P : Ideal C) [P.IsPrime] [P.LiesOver (maximalIdeal A)]
    [IsDomain (Localization.AtPrime P)] [_root_.IsDiscreteValuationRing (Localization.AtPrime P)]
    (hπP : algebraMap A (Localization.AtPrime P) π ≠ 0)
    {ϖ : Localization.AtPrime P} (hϖ : Irreducible ϖ) :
    ∃ u : (Localization.AtPrime P)ˣ,
      algebraMap A (Localization.AtPrime P) π = ↑u * ϖ ^ P.ramificationIdx A := by
  let B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) := by
    apply ((local_hom_tfae (algebraMap A B)).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A C B, ← Ideal.comap_comap, ← Ideal.under_def C,
      IsLocalization.AtPrime.under_maximalIdeal B P, ← Ideal.under_def,
      ← Ideal.over_def P (maximalIdeal A)]
  obtain ⟨u, hu⟩ := exists_unit_mul_pow_ramificationIdx hπ hπP hϖ
  have hmap_ne : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := fun hbot ↦
    hπP (Ideal.mem_bot.mp
      (hbot ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).mpr hπ.not_isUnit)))
  have he : P.ramificationIdx A = (maximalIdeal B).ramificationIdx A :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P _
      (map_maximalIdeal_eq_pow_ramificationIdx hmap_ne)
  exact ⟨u, he ▸ hu⟩

end

section Extension

variable {S T : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [_root_.IsDiscreteValuationRing T] [Algebra S T]
  [IsLocalHom (algebraMap S T)] [FaithfulSMul S T]

/-- For an extension of discrete valuation rings, the additive valuation of `T` restricts to `e`
times that of `S`, where `e` is the ramification index of the maximal ideal of `T` over `S`. -/
theorem addVal_algebraMap (s : S) :
    addVal T (algebraMap S T s) = (maximalIdeal T).ramificationIdx S • addVal S s := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  set e := (maximalIdeal T).ramificationIdx S
  -- `π T = 𝔪_T ^ e = ϖ ^ e T`, so `π` and `ϖ ^ e` are associated in `T`.
  have hne : (maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    simp [hπ.maximalIdeal_eq, Ideal.map_span, hπ.ne_zero]
  have hmap : Ideal.span {algebraMap S T π} = Ideal.span {ϖ ^ e} := by
    have h : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ e :=
      map_maximalIdeal_eq_pow_ramificationIdx hne
    simpa [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Ideal.span_singleton_pow]
      using h
  have hval : addVal T (algebraMap S T π) = e := by
    rw [(addVal_eq_iff_associated _ _).2 (Ideal.span_singleton_eq_span_singleton.1 hmap),
      hϖ.addVal_pow]
  rcases eq_or_ne s 0 with rfl | hs
  · -- `e ≠ 0`, so `e • ⊤ = ⊤`.
    have he : e ≠ 0 := (Ideal.ramificationIdx_pos_of_isDedekindDomain' (p := maximalIdeal S) _
      (not_a_field S)).ne'
    simp [he]
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hs hπ
  simp [hπ, hval, addVal_eq_zero_iff.2 (u.isUnit.map (algebraMap S T)), nsmul_eq_mul, mul_comm]

end Extension

end TauCeti.IsDiscreteValuationRing
