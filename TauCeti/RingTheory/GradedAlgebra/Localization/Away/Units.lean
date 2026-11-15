/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units
public import TauCeti.RingTheory.GradedAlgebra.Localization.Away.Basic
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
import TauCeti.RingTheory.Localization.Away.Units

/-!
# Homogeneous units of localizations away from homogeneous primes

Let `A` be a cancellative commutative `R`-algebra graded by an abelian group `ι` through
`𝒜 : ι → Submodule R A`, and let `f ∈ 𝒜 e`. Inverting `f` makes `f` a homogeneous unit of degree
`e` in `Localization.Away f`, so `homogeneousUnitDegrees (awayGrading 𝒜 hf)` always contains both
`homogeneousUnitDegrees 𝒜` and `AddSubgroup.zmultiples e`.

When `f` is prime, no further homogeneous unit degrees appear: clearing denominators expresses
every unit of `Localization.Away f` as a unit of `A` times an integral power of `f`, and cancelling
the regular homogeneous powers of `f` shows that the unit of `A` is itself homogeneous. Thus
`homogeneousUnitDegrees (awayGrading 𝒜 hf) = homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e`.
More generally, when `f = ∏ j ∈ s, g j` is a finite product of homogeneous primes `g j ∈ 𝒜 (e j)`,
`homogeneousUnitDegrees (awayGrading 𝒜 hf)` is the join of `homogeneousUnitDegrees 𝒜` with the
subgroups `AddSubgroup.zmultiples (e j)` for `j ∈ s`.

When `homogeneousUnitDegrees 𝒜 = ⊥` and `ι = ℤ`, inverting a prime `f ∈ 𝒜 e` identifies the shift
class group `ShiftClassGroup (awayGrading 𝒜 hf)` with `ZMod e.natAbs`.

## Main results

* `TauCeti.GradedAlgebra.algebraMap_mem_awayGrading_iff`: when `f` is regular, the localization map
  `A → Localization.Away f` reflects homogeneity in every degree.
* `TauCeti.homogeneousUnitDegrees_awayGrading_pow`: for any `p ∈ 𝒜 e` and `m ≠ 0`, inverting
  `p ^ m` gives the same homogeneous unit degrees as inverting `p`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_of_prime` and
  `TauCeti.homogeneousUnitDegrees_awayGrading_pow_of_prime`: for a prime `p ∈ 𝒜 e` (or positive
  power `p ^ m`), the homogeneous unit degrees are
  `homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_prod_of_prime`: for a product of homogeneous primes
  `g j ∈ 𝒜 (e j)`, `homogeneousUnitDegrees (awayGrading 𝒜 hf)` is
  `homogeneousUnitDegrees 𝒜 ⊔ ⨆ j ∈ s, AddSubgroup.zmultiples (e j)`.
* `TauCeti.shiftClassGroupAwayGradingEquiv`: when `homogeneousUnitDegrees 𝒜 = ⊥` and `f ∈ 𝒜 e` is
  prime in a `ℤ`-graded algebra, `ShiftClassGroup (awayGrading 𝒜 hf) ≃+ ZMod e.natAbs`.
-/

public section

namespace TauCeti.GradedAlgebra

variable {ι R A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommSemiring R] [CommSemiring A]
  [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {f : A} {e : ι} (hf : f ∈ 𝒜 e)

/-- When `f` is regular, the localization map `A → Localization.Away f` is injective, so an image
`algebraMap A (Localization.Away f) a` has degree `d` in `awayGrading 𝒜 hf` if and only if
`a ∈ 𝒜 d`. -/
theorem algebraMap_mem_awayGrading_iff (hreg : IsRegular f) {d : ι} {a : A} :
    algebraMap A (Localization.Away f) a ∈ awayGrading 𝒜 hf d ↔ a ∈ 𝒜 d := by
  have hinj : Function.Injective (awayGradedAlgHom 𝒜 hf) := by
    rw [coe_awayGradedAlgHom]
    exact IsLocalization.injectiveₛ (Localization.Away f) (M := Submonoid.powers f)
      (by rintro _ ⟨n, rfl⟩; exact hreg.pow n)
  simpa using Graded.map_mem_iff_of_injective (awayGradedAlgHom 𝒜 hf) hinj (i := d) (x := a)

end TauCeti.GradedAlgebra

namespace TauCeti

open _root_.TauCeti.GradedAlgebra

section GradedMonoid

variable {ι R A : Type*} [AddCommGroup ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜] {f : A} {e : ι} (hf : f ∈ 𝒜 e)

/-- For `f ∈ 𝒜 e`, the degree `e` of `f` lies in `homogeneousUnitDegrees (awayGrading 𝒜 hf)`,
since `algebraMap A (Localization.Away f) f` is a homogeneous unit of degree `e`. -/
theorem mem_homogeneousUnitDegrees_awayGrading :
    e ∈ homogeneousUnitDegrees (awayGrading 𝒜 hf) :=
  mem_homogeneousUnitDegrees_of_mem
    (u := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).unit)
    (by simpa using algebraMap_mem_awayGrading hf)

/-- Homogeneous unit degrees of `A` and multiples of the degree `e` of `f` are homogeneous unit
degrees of `Localization.Away f`. -/
theorem sup_zmultiples_le_homogeneousUnitDegrees_awayGrading :
    homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e ≤
      homogeneousUnitDegrees (awayGrading 𝒜 hf) := by
  refine sup_le (homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_)
    (AddSubgroup.zmultiples_le_of_mem (mem_homogeneousUnitDegrees_awayGrading 𝒜 hf))
  exact mem_homogeneousUnitDegrees_of_mem
    (u := Units.map (algebraMap A (Localization.Away f) : A →* Localization.Away f) u)
    (algebraMap_mem_awayGrading hu)

/-- When `f = ∏ j ∈ s, g j` with `g j ∈ 𝒜 (e j)`, the homogeneous unit degrees of
`Localization.Away f` contain `homogeneousUnitDegrees 𝒜` and `AddSubgroup.zmultiples (e j)` for
every `j ∈ s`. -/
theorem sup_iSup_zmultiples_le_homogeneousUnitDegrees_awayGrading_prod {J : Type*} {s : Finset J}
    {g : J → A} {e : J → ι} {e₀ : ι} (hg : ∀ j ∈ s, g j ∈ 𝒜 (e j))
    (hf : ∏ j ∈ s, g j ∈ 𝒜 e₀) :
    homogeneousUnitDegrees 𝒜 ⊔ (⨆ j ∈ s, AddSubgroup.zmultiples (e j)) ≤
      homogeneousUnitDegrees (awayGrading 𝒜 hf) := by
  refine sup_le ((le_sup_left.trans
      (sup_zmultiples_le_homogeneousUnitDegrees_awayGrading 𝒜 hf)))
    (iSup₂_le fun j hj ↦ AddSubgroup.zmultiples_le_of_mem ?_)
  have hunit : IsUnit (algebraMap A (Localization.Away (∏ i ∈ s, g i)) (g j)) :=
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hj))
      (IsLocalization.Away.algebraMap_isUnit (∏ i ∈ s, g i))
  exact mem_homogeneousUnitDegrees_of_mem (u := hunit.unit)
    (by simpa using algebraMap_mem_awayGrading (hg j hj))

/-- Inverting a positive power `p ^ m` (`m ≠ 0`) of a homogeneous element `p ∈ 𝒜 e` produces the
same homogeneous unit degrees as inverting `p`, since the mutual localization lifts preserve degree.
-/
theorem homogeneousUnitDegrees_awayGrading_pow {p : A} {e : ι} (hp : p ∈ 𝒜 e) {m : ℕ}
    (hm : m ≠ 0) (hf : p ^ m ∈ 𝒜 (m • e) := SetLike.pow_mem_graded m hp) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = homogeneousUnitDegrees (awayGrading 𝒜 hp) := by
  have hm1 : 1 + (m - 1) = m := Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr hm)
  have hp_unit : IsUnit (algebraMap A (Localization.Away (p ^ m)) p) :=
    IsLocalization.Away.isUnit_of_dvd (p ^ m) (dvd_pow_self p hm)
  have hpm_unit : IsUnit (algebraMap A (Localization.Away p) (p ^ m)) :=
    map_pow (algebraMap A (Localization.Away p)) p m ▸
      IsLocalization.Away.algebraMap_pow_isUnit p m
  let ψ : Localization.Away (p ^ m) →+* Localization.Away p :=
    IsLocalization.Away.lift (p ^ m) hpm_unit
  let φ : Localization.Away p →+* Localization.Away (p ^ m) :=
    IsLocalization.Away.lift p hp_unit
  have hmk {x c : A} (k : ℕ) :
      Localization.mk c (Submonoid.pow x k) * algebraMap A (Localization.Away x) x ^ k =
        algebraMap A (Localization.Away x) c := by
    simpa [Localization.mk_eq_mk'_apply, Submonoid.pow_apply] using
      IsLocalization.mk'_spec (Localization.Away x) c (Submonoid.pow x k)
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_)
    (homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_)
  · obtain ⟨n, b, hb, hub⟩ := mem_awayGrading_iff.mp hu
    refine mem_homogeneousUnitDegrees_of_mem (u := Units.map (ψ : _ →* _) u) ?_
    have hψ : ψ (u : Localization.Away (p ^ m)) = Localization.mk b (Submonoid.pow p (m * n)) := by
      refine ((IsLocalization.Away.algebraMap_isUnit p).pow (m * n)).mul_left_inj.mp ?_
      rw [hmk (m * n), pow_mul, ← map_pow, ← IsLocalization.Away.lift_eq
        (S := Localization.Away (p ^ m)) (p ^ m) hpm_unit (p ^ m), ← map_pow, ← map_mul, hub,
        hmk n, IsLocalization.Away.lift_eq]
    simpa [hψ] using mk_mem_awayGrading (hf := hp) (by rwa [mul_nsmul])
  · obtain ⟨n, a, ha, hua⟩ := mem_awayGrading_iff.mp hu
    have hmn : n + (m - 1) * n = m * n := by
      calc n + (m - 1) * n = 1 * n + (m - 1) * n := by rw [one_mul]
        _ = m * n := by rw [← add_mul, hm1]
    refine mem_homogeneousUnitDegrees_of_mem (u := Units.map (φ : _ →* _) u) ?_
    have hφ : φ (u : Localization.Away p) =
        Localization.mk (a * p ^ ((m - 1) * n)) (Submonoid.pow (p ^ m) n) := by
      refine ((hp_unit.pow n).mul
        ((IsLocalization.Away.algebraMap_isUnit (p ^ m)).pow n)).mul_left_inj.mp ?_
      have hlhs : φ u * algebraMap A (Localization.Away (p ^ m)) p ^ n =
          algebraMap A (Localization.Away (p ^ m)) a := by
        rw [← IsLocalization.Away.lift_eq (S := Localization.Away p) p hp_unit p, ← map_pow,
          ← map_mul, hua, hmk n, IsLocalization.Away.lift_eq]
      rw [← mul_assoc, hlhs, ← mul_assoc, mul_right_comm _ (algebraMap A _ p ^ n), hmk n,
        ← map_pow, ← map_pow, ← map_mul, ← map_mul, mul_assoc, ← pow_add, add_comm, hmn, pow_mul]
    have hmem := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded ((m - 1) * n) hp)
    rw [add_assoc, ← add_nsmul, hmn, mul_nsmul] at hmem
    simpa [hφ] using mk_mem_awayGrading (hf := hf) hmem

end GradedMonoid

section Prime

variable {ι R A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommSemiring R] [CommSemiring A]
  [IsCancelMulZero A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-- **Homogeneous unit degrees after inverting a homogeneous prime.** In a cancellative graded
`R`-algebra `A`, if `f ∈ 𝒜 e` is prime, the homogeneous unit degrees of `Localization.Away f` are
generated by those of `A` together with `e`. -/
theorem homogeneousUnitDegrees_awayGrading_of_prime {f : A} {e : ι} (hf : f ∈ 𝒜 e)
    (hprime : Prime f) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) =
      homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun z d hz ↦ ?_)
    (sup_zmultiples_le_homogeneousUnitDegrees_awayGrading 𝒜 hf)
  nontriviality A
  have hfreg : IsRegular f := ⟨mul_right_injective₀ hprime.ne_zero,
    mul_left_injective₀ hprime.ne_zero⟩
  obtain ⟨u, i, n, hzu⟩ := (IsLocalization.Away.isUnit_iff_of_prime hprime).mp z.isUnit
  -- Clearing `f ^ n` turns `z` into the image of `u * f ^ i` in degree `d + n • e`.
  have hmul : algebraMap A (Localization.Away f) ((u : A) * f ^ i) ∈
      awayGrading 𝒜 hf (d + n • e) := by
    rw [map_mul, map_pow, ← hzu, ← map_pow]
    exact SetLike.mul_mem_graded hz (algebraMap_mem_awayGrading (SetLike.pow_mem_graded n hf))
  have hmemA : f ^ i * (u : A) ∈ 𝒜 (i • e + (d + n • e - i • e)) := by
    rw [mul_comm, add_sub_cancel]
    exact (algebraMap_mem_awayGrading_iff 𝒜 hf hfreg).mp hmul
  have hu : (u : A) ∈ 𝒜 (d + n • e - i • e) :=
    mem_of_mul_mem_add_of_isLeftRegular 𝒜 (SetLike.pow_mem_graded i hf)
      (mul_right_injective₀ (pow_ne_zero i hprime.ne_zero)) hmemA
  have hd_eq : d = (d + n • e - i • e) + (i • e - n • e) := by abel
  rw [hd_eq]
  exact add_mem (AddSubgroup.mem_sup_left (mem_homogeneousUnitDegrees_of_mem hu))
    (AddSubgroup.mem_sup_right (sub_mem
      (nsmul_mem (AddSubgroup.mem_zmultiples e) i)
      (nsmul_mem (AddSubgroup.mem_zmultiples e) n)))

/-- When `homogeneousUnitDegrees 𝒜 = ⊥` and `f ∈ 𝒜 e` is prime, the homogeneous unit degrees of
`Localization.Away f` are the integer multiples of `e`. -/
theorem homogeneousUnitDegrees_awayGrading_eq_zmultiples_of_prime {f : A} {e : ι} (hf : f ∈ 𝒜 e)
    (hbot : homogeneousUnitDegrees 𝒜 = ⊥) (hprime : Prime f) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = AddSubgroup.zmultiples e := by
  rw [homogeneousUnitDegrees_awayGrading_of_prime 𝒜 hf hprime, hbot, bot_sup_eq]

/-- Inverting a positive power `p ^ m` (`m ≠ 0`) of a homogeneous prime `p ∈ 𝒜 e` generates `e` (not
merely `m • e`, the degree of `p ^ m`) in `homogeneousUnitDegrees`. -/
theorem homogeneousUnitDegrees_awayGrading_pow_of_prime {p : A} {e : ι} (hp : p ∈ 𝒜 e)
    (hprime : Prime p) {m : ℕ} (hm : m ≠ 0)
    (hf : p ^ m ∈ 𝒜 (m • e) := SetLike.pow_mem_graded m hp) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) =
      homogeneousUnitDegrees 𝒜 ⊔ AddSubgroup.zmultiples e := by
  rw [homogeneousUnitDegrees_awayGrading_pow 𝒜 hp hm hf,
    homogeneousUnitDegrees_awayGrading_of_prime 𝒜 hp hprime]

/-- **Homogeneous unit degrees after inverting a product of homogeneous primes.** In a cancellative
graded `R`-algebra `A`, if `g j ∈ 𝒜 (e j)` is prime for every `j ∈ s`, the homogeneous unit
degrees of `Localization.Away (∏ j ∈ s, g j)` are generated by those of `A` together with the
degrees `e j` for `j ∈ s`. -/
theorem homogeneousUnitDegrees_awayGrading_prod_of_prime {J : Type*} {s : Finset J}
    {g : J → A} {e : J → ι} (hg : ∀ j ∈ s, g j ∈ 𝒜 (e j)) (hprime : ∀ j ∈ s, Prime (g j))
    (hf : ∏ j ∈ s, g j ∈ 𝒜 (∑ j ∈ s, e j) := SetLike.prod_mem_graded 𝒜 e g hg) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) =
      homogeneousUnitDegrees 𝒜 ⊔ ⨆ j ∈ s, AddSubgroup.zmultiples (e j) := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun z d hz ↦ ?_)
    (sup_iSup_zmultiples_le_homogeneousUnitDegrees_awayGrading_prod 𝒜 hg hf)
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (Localization.Away (∏ j ∈ s, g j)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (∏ j ∈ s, g j))
        (Subsingleton.elim (0 : A) 1 ▸ one_mem _)
    simp [homogeneousUnitDegrees_eq_top_of_subsingleton]
  have hF0 : ∏ j ∈ s, g j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ (hprime j hj).ne_zero
  have hFreg : IsRegular (∏ j ∈ s, g j) := ⟨mul_right_injective₀ hF0, mul_left_injective₀ hF0⟩
  obtain ⟨u, k, n, hzu⟩ := (IsLocalization.Away.isUnit_iff_of_prod_prime hprime).mp z.isUnit
  -- Clearing `(∏ j ∈ s, g j) ^ n` expresses `z` as `u * ∏ j ∈ s, g j ^ k j` in `A`.
  have hmul : algebraMap A (Localization.Away (∏ j ∈ s, g j))
      ((u : A) * ∏ j ∈ s, g j ^ k j) ∈ awayGrading 𝒜 hf (d + n • ∑ j ∈ s, e j) := by
    rw [map_mul, map_prod]
    simp only [map_pow]
    rw [← hzu, ← map_pow]
    exact SetLike.mul_mem_graded hz (algebraMap_mem_awayGrading (SetLike.pow_mem_graded n hf))
  have hP_mem : ∏ j ∈ s, g j ^ k j ∈ 𝒜 (∑ j ∈ s, k j • e j) :=
    SetLike.prod_pow_mem_graded 𝒜 e g k hg
  have hP_ne : ∏ j ∈ s, g j ^ k j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ pow_ne_zero (k j) (hprime j hj).ne_zero
  have hmemA : (∏ j ∈ s, g j ^ k j) * (u : A) ∈
      𝒜 ((∑ j ∈ s, k j • e j) + (d + n • (∑ j ∈ s, e j) - ∑ j ∈ s, k j • e j)) := by
    rw [mul_comm, add_sub_cancel]
    exact (algebraMap_mem_awayGrading_iff 𝒜 hf hFreg).mp hmul
  have hu : (u : A) ∈ 𝒜 (d + n • (∑ j ∈ s, e j) - ∑ j ∈ s, k j • e j) :=
    mem_of_mul_mem_add_of_isLeftRegular 𝒜 hP_mem (mul_right_injective₀ hP_ne) hmemA
  have hd_eq : d = (d + n • (∑ j ∈ s, e j) - ∑ j ∈ s, k j • e j) +
      ((∑ j ∈ s, k j • e j) - n • ∑ j ∈ s, e j) := by abel
  rw [hd_eq]
  refine add_mem (AddSubgroup.mem_sup_left (mem_homogeneousUnitDegrees_of_mem hu))
    (AddSubgroup.mem_sup_right (sub_mem ?_ ?_))
  · exact sum_mem fun j hj ↦
      le_iSup₂ (f := fun j _ ↦ AddSubgroup.zmultiples (e j)) j hj
        (nsmul_mem (AddSubgroup.mem_zmultiples (e j)) (k j))
  · rw [Finset.smul_sum]
    exact sum_mem fun j hj ↦
      le_iSup₂ (f := fun j _ ↦ AddSubgroup.zmultiples (e j)) j hj
        (nsmul_mem (AddSubgroup.mem_zmultiples (e j)) n)

/-- When `homogeneousUnitDegrees 𝒜 = ⊥` and `g j ∈ 𝒜 (e j)` is prime for each `j ∈ s`, the
homogeneous unit degrees of `Localization.Away (∏ j ∈ s, g j)` form the subgroup generated by the
degrees `{e j | j ∈ s}`. -/
theorem homogeneousUnitDegrees_awayGrading_prod_eq_closure_of_prime {J : Type*} {s : Finset J}
    {g : J → A} {e : J → ι} (hbot : homogeneousUnitDegrees 𝒜 = ⊥)
    (hg : ∀ j ∈ s, g j ∈ 𝒜 (e j)) (hprime : ∀ j ∈ s, Prime (g j))
    (hf : ∏ j ∈ s, g j ∈ 𝒜 (∑ j ∈ s, e j) := SetLike.prod_mem_graded 𝒜 e g hg) :
    homogeneousUnitDegrees (awayGrading 𝒜 hf) = AddSubgroup.closure (e '' (s : Set J)) := by
  rw [homogeneousUnitDegrees_awayGrading_prod_of_prime 𝒜 hg hprime hf, hbot, bot_sup_eq]
  refine le_antisymm (iSup₂_le fun j hj ↦ AddSubgroup.zmultiples_le_of_mem ?_) ?_
  · exact AddSubgroup.subset_closure ⟨j, hj, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact le_iSup₂ (f := fun j _ ↦ AddSubgroup.zmultiples (e j)) j hj
      (AddSubgroup.mem_zmultiples (e j))

end Prime

section ShiftClassGroup

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [IsCancelMulZero A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {e : ℤ} (hf : f ∈ 𝒜 e)

/-- For a cancellative `ℤ`-graded `R`-algebra `A` with `homogeneousUnitDegrees 𝒜 = ⊥` and a prime
`f ∈ 𝒜 e`, the shift class group of `Localization.Away f` is `ZMod |e|`. -/
def shiftClassGroupAwayGradingEquiv (hbot : homogeneousUnitDegrees 𝒜 = ⊥) (hprime : Prime f) :
    ShiftClassGroup (awayGrading 𝒜 hf) ≃+ ZMod e.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_awayGrading_eq_zmultiples_of_prime 𝒜 hf hbot hprime)).trans
    (Int.quotientZMultiplesEquivZMod e)

/-- `shiftClassGroupAwayGradingEquiv` sends the class of a shift `d` to `d mod |e|`. -/
@[simp]
theorem shiftClassGroupAwayGradingEquiv_mk (hbot : homogeneousUnitDegrees 𝒜 = ⊥)
    (hprime : Prime f) (d : ℤ) :
    shiftClassGroupAwayGradingEquiv 𝒜 hf hbot hprime
      (d : ShiftClassGroup (awayGrading 𝒜 hf)) = d :=
  -- Both quotient equivalences compute by casting representatives `ℤ → ZMod |e|`.
  (rfl)

end ShiftClassGroup

end TauCeti
