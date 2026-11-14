/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import TauCeti.RingTheory.LocalRing.Etale
import TauCeti.RingTheory.Localization.Annihilator

/-!
# Locally principal ideals in finite algebras over local rings

Let `B` be a commutative ring with finitely many maximal ideals, such as a finite algebra over a
local ring `R` (`TauCeti.IsLocalRing.finite_maximalSpectrum_of_module_finite`). Every ideal `I` of
`B` whose localization at each maximal ideal is principal is globally principal
(`Ideal.exists_eq_span_singleton_of_finite_maximalSpectrum`), without any domain or Noetherianity
hypothesis: clearing unit denominators gives local generators `a_M ∈ I` of `I_M`, and Chinese
remainder coefficients `c_M` congruent to `1` modulo `M` and `0` modulo other maximal ideals
combine into `u = ∑_M c_M a_M`, which is an associate of `a_M` in each `B_M`. If an ideal `J` is
locally the annihilator of `I` at every maximal ideal, then `J = Ann(u)` globally since
annihilators of principal ideals commute with localization.

## Main results

* `TauCeti.IsLocalRing.finite_maximalSpectrum_of_module_finite`: a commutative algebra which is
  module-finite over a local ring has only finitely many maximal ideals.
* `Ideal.exists_eq_span_singleton_of_finite_maximalSpectrum`: over a commutative ring with finitely
  many maximal ideals, an ideal that is principal at every maximal ideal is principal.
* `Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum`: if in addition `J` is
  locally the annihilator of `I` at every maximal ideal, the generator `u` of `I` has annihilator
  `J`.
* `Ideal.exists_eq_span_singleton_of_isLocalRing` and
  `Ideal.exists_eq_span_singleton_and_annihilator_of_isLocalRing`: specializations to a finite
  algebra over a local ring.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter II, §5, no. 3, Proposition 5.
-/

public section

open Function

namespace TauCeti.IsLocalRing

/-- **A finite algebra over a local ring is semilocal.** Every maximal ideal of `B` contains the
extended maximal ideal `𝔪_R B`, and `B ⧸ 𝔪_R B` is finite over the residue field `R ⧸ 𝔪_R`, hence
Artinian with finitely many prime ideals. -/
theorem finite_maximalSpectrum_of_module_finite (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  let p := IsLocalRing.maximalIdeal R
  let pB := p.map (algebraMap R B)
  let _ : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (R ⧸ p) (B ⧸ pB) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (B ⧸ pB) := IsArtinianRing.of_finite (R ⧸ p) (B ⧸ pB)
  refine Finite.of_injective (β := PrimeSpectrum (B ⧸ pB))
    (fun M ↦ ⟨M.asIdeal.map (Ideal.Quotient.mk pB),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by simpa [Ideal.mk_ker] using map_maximalIdeal_le_of_isMaximal M.isMaximal)⟩)
    fun M₁ M₂ h ↦ MaximalSpectrum.ext ?_
  have hcomap := congrArg (fun q : PrimeSpectrum (B ⧸ pB) ↦ q.asIdeal.comap (Ideal.Quotient.mk pB))
    h
  rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.mpr (map_maximalIdeal_le_of_isMaximal (R := R) M₁.isMaximal),
    sup_eq_left.mpr (map_maximalIdeal_le_of_isMaximal (R := R) M₂.isMaximal)] at hcomap

end TauCeti.IsLocalRing

namespace Ideal

private lemma exists_mem_map_atPrime_eq_span_singleton {B : Type*} [CommRing B] (I M : Ideal B)
    [M.IsPrime] {x : Localization.AtPrime M}
    (hx : I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x}) :
    ∃ a ∈ I, I.map (algebraMap B (Localization.AtPrime M)) =
      Ideal.span {algebraMap B (Localization.AtPrime M) a} := by
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl x
  obtain ⟨t, ht, htb⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff M.primeCompl _ _ _ _).mp
    (hx ▸ Ideal.subset_span rfl)
  refine ⟨t * b, htb, hx.trans ?_⟩
  have hu := (IsLocalization.map_units (Localization.AtPrime M) ⟨t, ht⟩).mul
    (IsLocalization.map_units (Localization.AtPrime M) s)
  have hmul : algebraMap B (Localization.AtPrime M) (t * b) =
      (algebraMap B _ t * algebraMap B _ s) * IsLocalization.mk' (Localization.AtPrime M) b s := by
    rw [map_mul, mul_assoc, mul_comm (algebraMap B _ s), IsLocalization.mk'_spec]
  rw [hmul, Ideal.span_singleton_mul_left_unit hu]

private lemma span_singleton_sum_eq_atPrime {B : Type*} [CommRing B] [Fintype (MaximalSpectrum B)]
    (a c : MaximalSpectrum B → B) (m : MaximalSpectrum B)
    (hdiv : ∀ j, algebraMap B (Localization.AtPrime m.asIdeal) (a j) ∈
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)})
    (hcm : c m - 1 ∈ m.asIdeal) (hcj : ∀ {j}, j ≠ m → c j ∈ m.asIdeal) :
    Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (∑ j, c j * a j)} =
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)} := by
  classical
  have := m.isMaximal
  choose q hq using fun j ↦ Ideal.mem_span_singleton.mp (hdiv j)
  let f := algebraMap B (Localization.AtPrime m.asIdeal)
  set v : Localization.AtPrime m.asIdeal := f (c m) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j
  have hsum : f (∑ j, c j * a j) = v * f (a m) := by
    rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_mul, add_mul, Finset.sum_mul]
    exact congrArg (f (c m) * f (a m) + ·)
      (Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, hq j]; ring)
  have hv : IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal]; intro hvm
    have hm1 : v - 1 ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) := by
      rw [show v - 1 = f (c m - 1) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j by
        simp [v, sub_eq_add_neg, add_right_comm], ← Localization.AtPrime.map_eq_maximalIdeal]
      exact add_mem (Ideal.mem_map_of_mem _ hcm) (Submodule.sum_mem _ fun j hj ↦
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcj (Finset.ne_of_mem_erase hj))))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (sub_sub_cancel v 1 ▸ sub_mem hvm hm1) isUnit_one)
  rw [hsum, Ideal.span_singleton_mul_left_unit hv]

/-- **Locally principal ideals over a semilocal ring are principal.** Let `B` be a commutative ring
with finitely many maximal ideals. Any ideal `I` of `B` whose extension to `Localization.AtPrime M`
is principal for every maximal ideal `M` of `B` is generated by a single element. -/
theorem exists_eq_span_singleton_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I : Ideal B)
    (hI : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x}) :
    ∃ u : B, I = Ideal.span {u} := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  choose a haI ha using fun m : MaximalSpectrum B ↦
    have := m.isMaximal
    let ⟨x, hx⟩ := hI m.asIdeal
    exists_mem_map_atPrime_eq_span_singleton I m.asIdeal hx
  have hcop : Pairwise (IsCoprime on fun m : MaximalSpectrum B ↦ m.asIdeal) := fun m₁ m₂ hm ↦
    have := m₁.isMaximal; have := m₂.isMaximal
    Ideal.isCoprime_of_isMaximal fun heq ↦ hm (MaximalSpectrum.ext heq)
  choose c hc using fun i : MaximalSpectrum B ↦
    Ideal.pi_quotient_surjective hcop (Pi.single i 1)
  refine ⟨∑ j : MaximalSpectrum B, c j * a j, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  let m : MaximalSpectrum B := ⟨M, hM⟩
  rw [Ideal.map_span, Set.image_singleton, ha m, eq_comm]
  refine span_singleton_sum_eq_atPrime a c m (fun j ↦ ha m ▸ Ideal.mem_map_of_mem _ (haI j)) ?_
    fun {j} hj ↦ ?_
  · have h := hc m m
    rwa [Pi.single_eq_same, ← map_one (Ideal.Quotient.mk m.asIdeal), Ideal.Quotient.eq] at h
  · have h := hc j m
    rwa [Pi.single_eq_of_ne' hj, Ideal.Quotient.eq_zero_iff_mem] at h

/-- **Locally principal ideals and their annihilators over a semilocal ring.** If `B` has finitely
many maximal ideals, `I` is principal at every maximal ideal of `B`, and `J` agrees with the
annihilator of `I` at every maximal ideal of `B`, then `I = (u)` and `J = Ann(u)` for a single
element `u ∈ B`. -/
theorem exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I J : Ideal B)
    (hIJ : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x} ∧
        J.map (algebraMap B (Localization.AtPrime M)) = (Ideal.span {x}).annihilator) :
    ∃ u : B, I = Ideal.span {u} ∧ J = (Ideal.span {u}).annihilator := by
  obtain ⟨u, rfl⟩ := I.exists_eq_span_singleton_of_finite_maximalSpectrum
    fun M _ ↦ let ⟨x, hx, _⟩ := hIJ M; ⟨x, hx⟩
  refine ⟨u, rfl, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  obtain ⟨x, hx, hJ⟩ := hIJ M
  rw [Ideal.map_span, Set.image_singleton] at hx
  rw [hJ, ← hx, IsLocalization.map_annihilator_span_singleton M.primeCompl]

/-- **Locally principal ideals in a finite algebra over a local ring are principal.** -/
theorem exists_eq_span_singleton_of_isLocalRing (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] (I : Ideal B)
    (hI : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x}) :
    ∃ u : B, I = Ideal.span {u} :=
  have := TauCeti.IsLocalRing.finite_maximalSpectrum_of_module_finite R (B := B)
  I.exists_eq_span_singleton_of_finite_maximalSpectrum hI

/-- **Locally principal ideals and their annihilators in a finite algebra over a local ring.** -/
theorem exists_eq_span_singleton_and_annihilator_of_isLocalRing (R : Type*) {B : Type*}
    [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] (I J : Ideal B)
    (hIJ : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x} ∧
        J.map (algebraMap B (Localization.AtPrime M)) = (Ideal.span {x}).annihilator) :
    ∃ u : B, I = Ideal.span {u} ∧ J = (Ideal.span {u}).annihilator :=
  have := TauCeti.IsLocalRing.finite_maximalSpectrum_of_module_finite R (B := B)
  I.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum J hIJ

end Ideal
