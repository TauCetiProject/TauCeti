/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units
public import TauCeti.RingTheory.GradedAlgebra.Localization.Away
public import TauCeti.RingTheory.Localization.Away.Units

/-!
# Homogeneous unit degrees of a localization away from a homogeneous element

Let `A` be a commutative `R`-algebra graded by an additive commutative group `ι` through
`𝒜 : ι → Submodule R A`, and let `f ∈ 𝒜 e`. Under the localization grading `awayGrading 𝒜 hf` of
`Localization.Away f`, every homogeneous unit of `A` remains a homogeneous unit of the same degree,
and every homogeneous divisor `g ∈ 𝒜 d` of `f` (in particular `f` itself) becomes a homogeneous
unit of degree `d`.

When `A` is a domain and `f` is prime, no other degrees arise: every homogeneous unit `a / f ^ n`
of `Localization.Away f` has numerator `a` associated to a power `f ^ k`, so cancelling the nonzero
homogeneous factor `f ^ k` shows `deg a - k • e ∈ homogeneousUnitDegrees 𝒜`. Thus
`homogeneousUnitDegrees (awayGrading 𝒜 hf) = homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e`.
More generally, when `f = ∏ j ∈ s, p j` is a finite product of homogeneous primes `p j ∈ 𝒜 (d j)`,
the homogeneous unit degrees are `homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.closure (d '' s)`.

When `ι = ℤ` and `homogeneousUnitDegrees 𝒜 = ⊥`, inverting a homogeneous prime `f` of degree `e`
therefore gives `ShiftClassGroup (awayGrading 𝒜 hf) ≃+ ZMod e.natAbs`.

## Main definitions

* `TauCeti.shiftClassGroupAwayPrimeEquiv`: the equivalence
  `ShiftClassGroup (awayGrading 𝒜 hf) ≃+ ZMod e.natAbs` for a `ℤ`-graded domain with trivial
  homogeneous unit degrees localized at a homogeneous prime `f ∈ 𝒜 e`.

## Main results

* `TauCeti.homogeneousUnitDegrees_le_awayGrading` and
  `TauCeti.mem_homogeneousUnitDegrees_awayGrading_of_dvd`: containment of original homogeneous unit
  degrees and degrees of homogeneous divisors of `f`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_of_eq_zero` and
  `TauCeti.homogeneousUnitDegrees_awayGrading_of_isUnit`: boundary cases `f = 0` (`⊤`) and `f` a
  unit (`homogeneousUnitDegrees 𝒜`).
* `TauCeti.sub_mem_homogeneousUnitDegrees_of_associated`: in a graded domain, two nonzero
  associated homogeneous elements have degrees differing by an element of
  `homogeneousUnitDegrees 𝒜`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_of_prime` and
  `TauCeti.homogeneousUnitDegrees_awayGrading_prod_primes`: the homogeneous unit degrees of
  `awayGrading 𝒜 hf` when `f` is a homogeneous prime or a finite product of homogeneous primes.
-/

public section

namespace TauCeti

open TauCeti.GradedAlgebra TauCeti.Localization

section Semiring

variable {ι R A : Type*} [AddCommGroup ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  {𝒜 : ι → Submodule R A}

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜] {f : A} {e : ι} (hf : f ∈ 𝒜 e)

/-- Every homogeneous unit degree of `𝒜` remains a homogeneous unit degree of
`awayGrading 𝒜 hf`. -/
theorem homogeneousUnitDegrees_le_awayGrading :
    homogeneousUnitDegrees 𝒜 ≤ homogeneousUnitDegrees (awayGrading 𝒜 hf) :=
  homogeneousUnitDegrees_le_iff.mpr fun u _ hu ↦
    mem_homogeneousUnitDegrees_of_mem
      (u := Units.map (algebraMap A (Localization.Away f) : A →* _) u)
      (algebraMap_mem_awayGrading hu)

/-- Every homogeneous divisor `g ∈ 𝒜 d` of `f` becomes a homogeneous unit in
`Localization.Away f`, so `d ∈ homogeneousUnitDegrees (awayGrading 𝒜 hf)`. -/
theorem mem_homogeneousUnitDegrees_awayGrading_of_dvd {g : A} {d : ι} (hg : g ∈ 𝒜 d)
    (hdvd : g ∣ f) : d ∈ homogeneousUnitDegrees (awayGrading 𝒜 hf) := by
  refine mem_homogeneousUnitDegrees_of_mem (u := awayUnitOfDvd (Localization.Away f) hdvd) ?_
  rw [val_awayUnitOfDvd]
  exact algebraMap_mem_awayGrading hg

/-- The degree `e` of `f` itself belongs to `homogeneousUnitDegrees (awayGrading 𝒜 hf)`. -/
theorem mem_homogeneousUnitDegrees_awayGrading_self :
    e ∈ homogeneousUnitDegrees (awayGrading 𝒜 hf) :=
  mem_homogeneousUnitDegrees_awayGrading_of_dvd hf hf dvd_rfl

/-- All integer multiples of the degree `e` of `f` lie in
`homogeneousUnitDegrees (awayGrading 𝒜 hf)`. -/
theorem zmultiples_le_homogeneousUnitDegrees_awayGrading :
    AddSubgroup.zmultiples e ≤ homogeneousUnitDegrees (awayGrading 𝒜 hf) :=
  AddSubgroup.zmultiples_le.mpr (mem_homogeneousUnitDegrees_awayGrading_self hf)

/-- Localizing away from `0` collapses `Localization.Away f` to the zero ring, so every degree is
the degree of a homogeneous unit. -/
theorem homogeneousUnitDegrees_awayGrading_of_eq_zero (hf0 : f = 0) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = ⊤ := by
  have : Subsingleton (Localization.Away f) :=
    IsLocalization.subsingleton (M := Submonoid.powers f) (S := Localization.Away f)
      ⟨1, by simp [hf0]⟩
  exact homogeneousUnitDegrees_eq_top_of_subsingleton

end GradedMonoid

private theorem isUnit_algebraMap_of_eq_mk {f : A} {v : (Localization.Away f)ˣ} {n : ℕ} {a : A}
    (hv_eq : (v : Localization.Away f) = Localization.mk a (Submonoid.pow f n)) :
    IsUnit (algebraMap A (Localization.Away f) a) := by
  have hmap : algebraMap A (Localization.Away f) a =
      (v : Localization.Away f) * algebraMap A (Localization.Away f) (f ^ n) := by
    rw [hv_eq, Localization.mk_eq_mk'_apply]
    exact (IsLocalization.mk'_spec (Localization.Away f) a (Submonoid.pow f n)).symm
  rw [hmap, map_pow, ← val_awayUnit (Localization.Away f) f]
  exact v.isUnit.mul ((awayUnit (Localization.Away f) f).isUnit.pow n)

section GradedAlgebra

variable [DecidableEq ι] [GradedAlgebra 𝒜]

/-- Localizing away from a homogeneous unit `f` does not enlarge `homogeneousUnitDegrees`. -/
theorem homogeneousUnitDegrees_awayGrading_of_isUnit {f : A} {e : ι} (hf : f ∈ 𝒜 e)
    (hu : IsUnit f) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = homogeneousUnitDegrees 𝒜 := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun v d hv ↦ ?_)
    (homogeneousUnitDegrees_le_awayGrading hf)
  obtain ⟨n, a, ha, hv_eq⟩ := mem_awayGrading_iff.mp hv
  obtain ⟨k, hk⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away f) f).mp
    (isUnit_algebraMap_of_eq_mk hv_eq)
  have ha_unit : IsUnit a := isUnit_of_dvd_unit hk (hu.pow k)
  have had : d + n • e ∈ homogeneousUnitDegrees 𝒜 :=
    mem_homogeneousUnitDegrees_of_mem (u := ha_unit.unit) (by simpa using ha)
  have he : e ∈ homogeneousUnitDegrees 𝒜 :=
    mem_homogeneousUnitDegrees_of_mem (u := hu.unit) (by simpa using hf)
  have hsub := sub_mem had (nsmul_mem he n)
  simpa using hsub

@[simp]
theorem homogeneousUnitDegrees_awayGrading_one (h1 : (1 : A) ∈ 𝒜 (0 : ι)) :
    homogeneousUnitDegrees (awayGrading 𝒜 h1) = homogeneousUnitDegrees 𝒜 :=
  homogeneousUnitDegrees_awayGrading_of_isUnit h1 isUnit_one

end GradedAlgebra

end Semiring

section Domain

variable {ι R A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommSemiring R] [CommSemiring A]
  [IsDomain A] [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- In a graded domain, if a nonzero homogeneous element `b ∈ 𝒜 db` is associated to a homogeneous
element `a ∈ 𝒜 da`, then `da - db ∈ homogeneousUnitDegrees 𝒜`: the unit cofactor is homogeneous of
degree `da - db`. -/
theorem sub_mem_homogeneousUnitDegrees_of_associated {a b : A} {da db : ι} (ha : a ∈ 𝒜 da)
    (hb : b ∈ 𝒜 db) (hb0 : b ≠ 0) (h : Associated b a) :
    da - db ∈ homogeneousUnitDegrees 𝒜 := by
  obtain ⟨u, rfl⟩ := h
  have hu : (u : A) ∈ 𝒜 (da - db) :=
    mem_of_mul_mem_add_of_isLeftRegular 𝒜 hb (isRegular_iff_ne_zero.mpr hb0).left
      (by rwa [add_sub_cancel])
  exact mem_homogeneousUnitDegrees_of_mem hu

/-- **Homogeneous unit degrees away from a homogeneous prime.** In a graded domain `(A, 𝒜)`,
localizing away from a homogeneous prime `f ∈ 𝒜 e` adjoins `ℤ • e` to `homogeneousUnitDegrees 𝒜`. -/
theorem homogeneousUnitDegrees_awayGrading_of_prime {f : A} {e : ι} (hf : f ∈ 𝒜 e)
    (hprime : Prime f) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) =
      homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun v d hv ↦ ?_)
    (sup_le (homogeneousUnitDegrees_le_awayGrading hf)
      (zmultiples_le_homogeneousUnitDegrees_awayGrading hf))
  obtain ⟨n, a, ha, hv_eq⟩ := mem_awayGrading_iff.mp hv
  -- In a domain, `a` becoming a unit away from the prime `f` means `a` is associated to `f ^ k`.
  obtain ⟨k, hak⟩ := (hprime.isUnit_algebraMap_away_iff (S := Localization.Away f)).mp
    (isUnit_algebraMap_of_eq_mk hv_eq)
  have hfk_mem : f ^ k ∈ 𝒜 (k • e) := by simpa using SetLike.pow_mem_graded k hf
  have hsub : (d + n • e) - k • e ∈ homogeneousUnitDegrees 𝒜 :=
    sub_mem_homogeneousUnitDegrees_of_associated ha hfk_mem (pow_ne_zero k hprime.ne_zero) hak.symm
  have hz : ((k : ℤ) - (n : ℤ)) • e ∈ AddSubgroup.zmultiples e :=
    AddSubgroup.mem_zmultiples_iff.mpr ⟨(k : ℤ) - (n : ℤ), rfl⟩
  rw [AddSubgroup.mem_sup]
  refine ⟨(d + n • e) - k • e, hsub, ((k : ℤ) - (n : ℤ)) • e, hz, ?_⟩
  rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
  abel

/-- When `homogeneousUnitDegrees 𝒜 = ⊥`, localizing a graded domain away from a homogeneous prime
`f ∈ 𝒜 e` gives `homogeneousUnitDegrees (awayGrading 𝒜 hf) = AddSubgroup.zmultiples e`. -/
theorem homogeneousUnitDegrees_awayGrading_of_prime_of_eq_bot {f : A} {e : ι} (hf : f ∈ 𝒜 e)
    (hprime : Prime f) (hbot : homogeneousUnitDegrees 𝒜 = ⊥) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = AddSubgroup.zmultiples e := by
  rw [homogeneousUnitDegrees_awayGrading_of_prime hf hprime, hbot, bot_sup_eq]

/-- **Homogeneous unit degrees away from a product of homogeneous primes.** In a graded domain
`(A, 𝒜)`, if `p j ∈ 𝒜 (d j)` is prime for every `j ∈ s` and `(∏ j ∈ s, p j) ∈ 𝒜 e`, then
`homogeneousUnitDegrees (awayGrading 𝒜 hf)` is generated by `homogeneousUnitDegrees 𝒜` together
with the degrees `d j` (`j ∈ s`). No distinctness assumption on the primes `p j` is needed. -/
theorem homogeneousUnitDegrees_awayGrading_prod_primes {J : Type*} {s : Finset J}
    {p : J → A} {d : J → ι} {e : ι} (hp_mem : ∀ j ∈ s, p j ∈ 𝒜 (d j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hf : (∏ j ∈ s, p j) ∈ 𝒜 e) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) =
      homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.closure (d '' (s : Set J)) := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun v c hv ↦ ?_)
    (sup_le (homogeneousUnitDegrees_le_awayGrading hf) ?_)
  · obtain ⟨n, a, ha, hv_eq⟩ := mem_awayGrading_iff.mp hv
    obtain ⟨m, ham⟩ :=
      (s.isUnit_algebraMap_away_prod_primes_iff
        (S := Localization.Away (∏ j ∈ s, p j)) hp_prime).mp
        (isUnit_algebraMap_of_eq_mk hv_eq)
    have hprod_ne : ∏ j ∈ s, p j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj ↦ (hp_prime j hj).ne_zero
    have he_eq : e = ∑ j ∈ s, d j :=
      DirectSum.degree_eq_of_mem_mem 𝒜 hf (SetLike.prod_mem_graded 𝒜 d p hp_mem) hprod_ne
    have hpm_mem : (∏ j ∈ s, p j ^ m j) ∈ 𝒜 (∑ j ∈ s, m j • d j) :=
      SetLike.prod_pow_mem_graded 𝒜 d p m hp_mem
    have hpm_ne : ∏ j ∈ s, p j ^ m j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj ↦ pow_ne_zero (m j) (hp_prime j hj).ne_zero
    have hsub : (c + n • e) - ∑ j ∈ s, m j • d j ∈ homogeneousUnitDegrees 𝒜 :=
      sub_mem_homogeneousUnitDegrees_of_associated ha hpm_mem hpm_ne ham.symm
    have hcl_m : ∑ j ∈ s, m j • d j ∈ AddSubgroup.closure (d '' (s : Set J)) :=
      sum_mem fun j hj ↦ nsmul_mem (AddSubgroup.subset_closure (Set.mem_image_of_mem d hj)) (m j)
    have hcl_n : n • e ∈ AddSubgroup.closure (d '' (s : Set J)) := by
      rw [he_eq]
      exact nsmul_mem
        (sum_mem fun j hj ↦ AddSubgroup.subset_closure (Set.mem_image_of_mem d hj)) n
    rw [AddSubgroup.mem_sup]
    exact ⟨(c + n • e) - ∑ j ∈ s, m j • d j, hsub,
      (∑ j ∈ s, m j • d j) - n • e, sub_mem hcl_m hcl_n, by abel⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact mem_homogeneousUnitDegrees_awayGrading_of_dvd hf (hp_mem j hj)
      (Finset.dvd_prod_of_mem p hj)

/-- When `homogeneousUnitDegrees 𝒜 = ⊥`, localizing a graded domain away from a product of
homogeneous primes `p j ∈ 𝒜 (d j)` (`j ∈ s`) gives the subgroup generated by `d '' s`. -/
theorem homogeneousUnitDegrees_awayGrading_prod_primes_of_eq_bot {J : Type*} {s : Finset J}
    {p : J → A} {d : J → ι} {e : ι} (hp_mem : ∀ j ∈ s, p j ∈ 𝒜 (d j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hf : (∏ j ∈ s, p j) ∈ 𝒜 e)
    (hbot : homogeneousUnitDegrees 𝒜 = ⊥) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = AddSubgroup.closure (d '' (s : Set J)) := by
  rw [homogeneousUnitDegrees_awayGrading_prod_primes hp_mem hp_prime hf, hbot, bot_sup_eq]

end Domain

section IntShiftClass

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [IsDomain A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- For a `ℤ`-graded domain `(A, 𝒜)` with `homogeneousUnitDegrees 𝒜 = ⊥` and a homogeneous prime
`f ∈ 𝒜 e`, the shift class group `ShiftClassGroup (awayGrading 𝒜 hf)` is canonically isomorphic to
`ZMod e.natAbs`. -/
noncomputable def shiftClassGroupAwayPrimeEquiv {f : A} {e : ℤ} (hf : f ∈ 𝒜 e)
    (hprime : Prime f) (hbot : homogeneousUnitDegrees 𝒜 = ⊥) :
    ShiftClassGroup (awayGrading 𝒜 hf) ≃+ ZMod e.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_awayGrading_of_prime_of_eq_bot hf hprime hbot)).trans
    (Int.quotientZMultiplesEquivZMod e)

@[simp]
theorem shiftClassGroupAwayPrimeEquiv_mk {f : A} {e : ℤ} (hf : f ∈ 𝒜 e) (hprime : Prime f)
    (hbot : homogeneousUnitDegrees 𝒜 = ⊥) (d : ℤ) :
    shiftClassGroupAwayPrimeEquiv hf hprime hbot (QuotientAddGroup.mk d) = d := by
  -- Both quotient equivalences are induced by maps on representatives, and the second is the
  -- canonical cast `ℤ → ZMod |e|`; Mathlib states no lemma evaluating them on a class.
  rfl

end IntShiftClass

end TauCeti
