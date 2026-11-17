/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
import TauCeti.Algebra.Algebra.Tower

/-!
# Residue degree and ramification index under a change of rings

Let `R → S → T` be a tower of algebras. An ideal of `T` has the same residue degree over `R` as
over `S` when `algebraMap R S` is bijective, and the same ramification index when that map is
surjective. In particular, statements about two presentations of the same base ring, such as
`ℤ` and the ring of integers of `ℚ`, can be transported into each other. Dually, the
ramification index of an ideal over `R` is unchanged by an `R`-algebra isomorphism of the ring
containing it, so it does not depend on the chosen model of, say, an integral closure. Along a
flat integral extension `S → T`, each maximal ideal of `S` lies under a maximal ideal of `T`
whose ramification index it divides. For Dedekind domains `R` and `B` whose fraction fields are
identified by a surjective `algebraMap K L`, every prime ideal of `B` has ramification index `1`
over `R`.

## Main results

* `Ideal.inertiaDeg_eq_of_bijective`: `r.inertiaDeg S = r.inertiaDeg R`.
* `Ideal.ramificationIdx_eq_of_surjective`: `r.ramificationIdx S = r.ramificationIdx R`.
* `Ideal.ramificationIdx_map_algEquiv`: `(P.map e).ramificationIdx R = P.ramificationIdx R` for
  an `R`-algebra isomorphism `e`.
* `Ideal.exists_isMaximal_liesOver_ramificationIdx_dvd`: a maximal ideal `Q` of `S` lies under a
  maximal ideal `P` of `T` with `Q.ramificationIdx R ∣ P.ramificationIdx R`.
* `Ideal.ramificationIdx_eq_one_of_surjective_fractionRing`: if `algebraMap K L` between the
  fraction fields of Dedekind domains `R` and `B` is surjective, then every prime ideal of `B`
  has ramification index `1` over `R`.
-/

public section

namespace Ideal

section ChangeOfBase

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]

/-- An ideal has the same residue degree over `S` as over `R` when `algebraMap R S` is
bijective. -/
theorem inertiaDeg_eq_of_bijective (h : Function.Bijective (algebraMap R S)) (r : Ideal T) :
    r.inertiaDeg S = r.inertiaDeg R := by
  let e := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower S R T := .of_algebraMap_rightInverse e.apply_symm_apply
  exact Nat.dvd_antisymm (inertiaDeg_above_dvd (r.under S) r) (inertiaDeg_above_dvd (r.under R) r)

/-- An ideal has the same ramification index over `S` as over `R` when `algebraMap R S` is
surjective. -/
theorem ramificationIdx_eq_of_surjective
    (h : Function.Surjective (algebraMap R S)) (r : Ideal T) :
    r.ramificationIdx S = r.ramificationIdx R := by
  have hm : (r.under R).map (algebraMap R S) = r.under S := by
    rw [← under_under (A := R) (B := S) r]
    exact map_comap_of_surjective _ h _
  by_cases hr : r.IsPrime
  · rw [ramificationIdx_def, ramificationIdx_def,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime r), ← map_map, hm]
  · rw [ramificationIdx_of_not_isPrime r S hr, ramificationIdx_of_not_isPrime r R hr]

end ChangeOfBase

/-- The ramification index over `R` is invariant under `R`-algebra isomorphisms: the image of an
ideal `P` under `e : S ≃ₐ[R] T` has the same ramification index over `R` as `P`. -/
theorem ramificationIdx_map_algEquiv {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (P : Ideal S) :
    (P.map e).ramificationIdx R = P.ramificationIdx R := by
  by_cases hP : P.IsPrime
  swap
  · rw [ramificationIdx_of_not_isPrime _ _ hP, ramificationIdx_of_not_isPrime]
    intro h
    have := comap_isPrime e (K := P.map e)
    exact hP (by rwa [comap_map_of_bijective _ e.bijective] at this)
  -- View `e` as a flat, bijective `S`-algebra structure on `T`, and apply the tower formula.
  let : Algebra S T := e.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  have hbij : Function.Bijective (algebraMap S T) := e.bijective
  have : Module.Flat S T :=
    .of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap S T) hbij).symm
  have : (P.map e).LiesOver P := ⟨(comap_map_of_bijective _ hbij).symm⟩
  have : (P.map e).IsPrime := map_isPrime_of_equiv e
  rw [ramificationIdx_tower (q := P), ← ramificationIdx_eq_of_surjective hbij.2,
    ramificationIdx_eq_one (P.map e) T, mul_one]

/-- Going up along a flat integral extension `S → T` keeps track of ramification: every maximal
ideal `Q` of `S` lies under a maximal ideal `P` of `T` whose ramification index over `R` is
divisible by that of `Q`. -/
theorem exists_isMaximal_liesOver_ramificationIdx_dvd (R : Type*) {S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsIntegral S T] [FaithfulSMul S T] [Module.Flat S T] (Q : Ideal S) [Q.IsMaximal] :
    ∃ P : Ideal T, P.IsMaximal ∧ P.LiesOver Q ∧ Q.ramificationIdx R ∣ P.ramificationIdx R := by
  obtain ⟨P, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := T) Q
  exact ⟨P, ‹_›, ‹_›, ramificationIdx_below_dvd Q P⟩

/-- If `R` and `B` are Dedekind domains whose fraction fields `K` and `L` are linked by a
surjective `algebraMap K L`, then every prime ideal `q` of `B` has ramification index `1` over
`R`. -/
theorem ramificationIdx_eq_one_of_surjective_fractionRing
    {B : Type*} [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R B]
    {K L : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
    (h : Function.Surjective (algebraMap K L)) :
    q.ramificationIdx R = 1 := by
  rcases eq_or_ne q ⊥ with rfl | hq
  · exact Ideal.ramificationIdx_bot_eq_one R
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have hunder : q.under R ≠ ⊥ := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
    obtain ⟨x, hx⟩ := h (algebraMap B L b)
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have halg_s : algebraMap R K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0
    have hL : algebraMap B L (algebraMap R B r) = algebraMap B L (algebraMap R B s * b) := by
      rw [← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L,
        map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L,
        ← hx, map_div₀, mul_div_cancel₀ _
          ((map_ne_zero_iff _ (algebraMap K L).injective).mpr halg_s)]
    have hB : algebraMap R B r = algebraMap R B s * b := IsFractionRing.injective B L hL
    have hr_mem : r ∈ q.under R := by
      rw [Ideal.mem_under, hB]
      exact q.mul_mem_left _ hb
    have hr0 : r ≠ 0 := fun hr ↦
      mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R B)).mpr hs0) hb0
        (by rw [← hB, hr, map_zero])
    exact ne_of_mem_of_not_mem' hr_mem (by rw [Ideal.mem_bot]; exact hr0)
  let v : IsDedekindDomain.HeightOneSpectrum R := ⟨q.under R, inferInstance, hunder⟩
  let w : IsDedekindDomain.HeightOneSpectrum B := ⟨q, inferInstance, hq⟩
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  obtain ⟨x, hx⟩ := h π
  have hpow : v.valuation K x ^ w.asIdeal.ramificationIdx R = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (K := K) L v w x, hx, hπ]
  have he_ne : w.asIdeal.ramificationIdx R ≠ 0 :=
    (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne'
  have hx_ne : v.valuation K x ≠ 0 := by
    intro h0
    rw [h0, zero_pow he_ne] at hpow
    exact WithZero.exp_ne_zero hpow.symm
  have hmul : (w.asIdeal.ramificationIdx R : ℤ) * WithZero.log (v.valuation K x) = -1 := by
    rw [← WithZero.exp_log hx_ne, ← WithZero.exp_nsmul] at hpow
    simpa only [nsmul_eq_mul] using WithZero.exp_injective hpow
  have habs : w.asIdeal.ramificationIdx R * (WithZero.log (v.valuation K x)).natAbs = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_one] using
      congrArg Int.natAbs hmul
  exact Nat.eq_one_of_mul_eq_one_right habs

end Ideal
