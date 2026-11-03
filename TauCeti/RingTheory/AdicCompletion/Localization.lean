/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.AdicCompletion.AlgHom

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Completions of localizations

Let `R` be a noetherian ring, `J` an ideal of `R` and `S` a localization of `R` at a submonoid
`M`. This file shows that the completion `Ŝ` of `S` along `J S` is flat over the completion `R̂`
of `R` along `J`.

Write `T` for the localization of `R̂` at the image of `M`. The localization map `S → T` induces
bijections `S ⧸ J ^ n S → T ⧸ J ^ n T` for every `n`, because modulo `J ^ n` both rings are the
localization of `R ⧸ J ^ n` at `M`. Hence `Ŝ` is also the completion of `T` along `J T`. Now `T` is
flat over `R̂`, being a localization, and the completion of `T` is flat over `T`, because `T` is
noetherian.

Completed localizations of this kind are the rings of sections of formal spectra over basic open
sets. For instance, for an open prime `𝔭` of an adic noetherian ring `A` with ideal of definition
`I`, the completion of `A_𝔭` along `I A_𝔭` is flat over every completed localization `A_{f}` with
`f ∉ 𝔭`.

## Main results

* `AdicCompletion.flat_mapₐ_of_isLocalization`: the completion of a localization `S` of a
  noetherian ring `R` is flat over the completion of `R`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6.
-/

public section

namespace AdicCompletion

section Localization

variable {R : Type*} [CommRing R] (J : Ideal R) (M : Submonoid R) {S : Type*} [CommRing S]
  [Algebra R S] [IsLocalization M S]

/-- The localization of the completion `R̂` of `R` along `J` at the image of `M`. -/
private abbrev LocalizedCompletion : Type _ :=
  Localization (Algebra.algebraMapSubmonoid (AdicCompletion J R) M)

omit [IsLocalization M S] in
/-- The elements of `M` become units in the localization `T` of the completion. -/
private theorem isUnit_algebraMap (m : M) :
    IsUnit (algebraMap R (LocalizedCompletion J M) m) := by
  rw [IsScalarTower.algebraMap_apply R (AdicCompletion J R)]
  exact IsLocalization.map_units _ (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem m⟩ :
    Algebra.algebraMapSubmonoid (AdicCompletion J R) M)

/-- The localization map `S → T` from the localization of `R` to the localization `T` of its
completion. -/
private noncomputable def toLocalization : S →ₐ[R] LocalizedCompletion J M :=
  IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R _) (isUnit_algebraMap J M)

omit [IsLocalization M S] in
/-- The powers of `J T` are the extensions of the powers of `J R̂`. -/
private theorem map_pow_eq (n : ℕ) : (J.map (algebraMap R (LocalizedCompletion J M))) ^ n =
    ((J ^ n).map (algebraMap R (AdicCompletion J R))).map
      (algebraMap (AdicCompletion J R) (LocalizedCompletion J M)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow]

variable {J M} in
/-- The localization map `S → T` sends the ideal `J S` into `J T`. -/
private theorem le_comap_toLocalization {K : Ideal S} (hK : J.map (algebraMap R S) = K) :
    K ≤ (J.map (algebraMap R (LocalizedCompletion J M))).comap (toLocalization J M) := by
  rw [← hK, Ideal.map_le_iff_le_comap]
  intro j hj
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hj

/-- Modulo `J ^ n`, the localization of `R` and the localization `T` of its completion agree: the
map `S ⧸ J ^ n S → T ⧸ J ^ n T` is bijective. -/
private theorem bijective_quotientMap_toLocalization (hJ : J.FG) {K : Ideal S}
    (hK : J.map (algebraMap R S) = K) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((J.map (algebraMap R (LocalizedCompletion J M))) ^ n)
      (toLocalization J M).toRingHom
      ((Ideal.pow_right_mono (le_comap_toLocalization hK) n).trans (Ideal.le_comap_pow _ n))) := by
  refine ⟨Ideal.quotientMap_injective' fun s hs ↦ ?_, Ideal.Quotient.mk_surjective.forall.2
    fun t ↦ ?_⟩
  · -- if `s = r / m` lies in `J ^ n T`, then `m₀ r ∈ J ^ n` for some `m₀ ∈ M`
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M s
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hs
    have hr : algebraMap R (LocalizedCompletion J M) r ∈
        (J.map (algebraMap R (LocalizedCompletion J M))) ^ n := by
      rw [← AlgHom.commutes (toLocalization (S := S) J M), ← IsLocalization.mk'_spec S r m,
        map_mul]
      exact Ideal.mul_mem_right _ _ hs
    rw [map_pow_eq, IsScalarTower.algebraMap_apply R (AdicCompletion J R),
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Algebra.algebraMapSubmonoid (AdicCompletion J R) M)] at hr
    obtain ⟨_, ⟨m₀, hm₀, rfl⟩, hm⟩ := hr
    rw [← map_mul, AdicCompletion.algebraMap_mem_map_pow_iff hJ] at hm
    rw [← hK, ← Ideal.map_pow, ← Ideal.mul_unit_mem_iff_mem _
      (IsLocalization.map_units S (⟨m₀ * m, mul_mem hm₀ m.2⟩ : M)), map_mul,
      mul_left_comm, IsLocalization.mk'_spec, ← map_mul]
    exact Ideal.mem_map_of_mem _ hm
  · -- write `t = x / m₀` with `x ∈ R̂`, and `x ≡ r` modulo `J ^ n R̂` with `r ∈ R`
    obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (AdicCompletion J R) M) t
    obtain ⟨m₀, hm₀, hm⟩ := m.2
    obtain ⟨r, hr⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow hJ n x
    refine ⟨Ideal.Quotient.mk _ (IsLocalization.mk' S r ⟨m₀, hm₀⟩), ?_⟩
    -- after multiplying by the unit `m₀`, the difference is the image of `r - x ∈ J ^ n R̂`
    have ht : IsLocalization.mk' (LocalizedCompletion J M) x m *
        algebraMap R (LocalizedCompletion J M) m₀ =
          algebraMap (AdicCompletion J R) (LocalizedCompletion J M) x := by
      rw [IsScalarTower.algebraMap_apply R (AdicCompletion J R), hm, IsLocalization.mk'_spec]
    have hs : toLocalization J M (IsLocalization.mk' S r ⟨m₀, hm₀⟩) *
        algebraMap R (LocalizedCompletion J M) m₀ = algebraMap R (LocalizedCompletion J M) r := by
      rw [← AlgHom.commutes (toLocalization (S := S) J M) m₀, ← map_mul, IsLocalization.mk'_spec,
        AlgHom.commutes]
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← Ideal.mul_unit_mem_iff_mem _
      (isUnit_algebraMap J M ⟨m₀, hm₀⟩), sub_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, ht,
      IsScalarTower.algebraMap_apply R (AdicCompletion J R) _ r, ← map_sub, map_pow_eq, ← neg_sub,
      map_neg]
    exact neg_mem (Ideal.mem_map_of_mem _ hr)

include M in
/-- **The completion of a localization is flat over the completion.** Let `R` be a noetherian
ring, `J` an ideal of `R` and `S` a localization of `R` at a submonoid. Then the completion of `S`
along `J S` is flat over the completion of `R` along `J`. -/
theorem flat_mapₐ_of_isLocalization [IsNoetherianRing R] {K : Ideal S}
    (hK : J.map (algebraMap R S) = K) :
    (mapₐ (Algebra.ofId R S) (hK ▸ Ideal.le_comap_map) :
      AdicCompletion J R →ₐ[R] AdicCompletion K S).toRingHom.Flat := by
  have hJ : J.FG := IsNoetherian.noetherian J
  -- the completion of `S` is the completion of the localization `T` of `R̂`
  have he := bijective_mapₐ _ (le_comap_toLocalization hK)
    (bijective_quotientMap_toLocalization J M hJ hK)
  rw [← RingHom.Flat.comp_iff_of_bijective_left he]
  have hcomp : (mapₐ (toLocalization J M) (le_comap_toLocalization hK)).toRingHom.comp
      (mapₐ (Algebra.ofId R S) (hK ▸ Ideal.le_comap_map) :
        AdicCompletion J R →ₐ[R] AdicCompletion K S).toRingHom =
      (algebraMap (LocalizedCompletion J M)
        (AdicCompletion (J.map (algebraMap R (LocalizedCompletion J M)))
          (LocalizedCompletion J M))).comp
        (algebraMap (AdicCompletion J R) (LocalizedCompletion J M)) := by
    refine RingHom.ext fun x ↦ ext_evalₐ fun n ↦ ?_
    -- modulo `J ^ n`, the element `x` of the completion is the image of some `r ∈ R`
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow hJ n x
    have hx : evalₐ J n x = Ideal.Quotient.mk _ r := by
      rw [← ker_evalₐ_eq_map_pow hJ, RingHom.mem_ker, map_sub, sub_eq_zero] at hr
      simpa [algebraMap_apply] using hr
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evalₐ_mapₐ, hx,
      algebraMap_apply, evalₐ_of, Ideal.quotientMap_mk, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.ofId_apply, AlgHom.commutes, Ideal.Quotient.eq]
    rw [IsScalarTower.algebraMap_apply R (AdicCompletion J R), ← map_sub, map_pow_eq, ← neg_sub,
      map_neg]
    exact neg_mem (Ideal.mem_map_of_mem _ hr)
  -- `T` is flat over `R̂`, and its completion is flat over `T` since `T` is noetherian
  rw [hcomp]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

end Localization

end AdicCompletion
