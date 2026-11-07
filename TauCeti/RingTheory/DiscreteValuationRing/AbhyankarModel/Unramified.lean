/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.NatCast
public import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Eisenstein
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# The Kummer base of the Abhyankar model

Let `A → B` be a map of discrete valuation rings, with uniformizers `π` and `ϖ`,
and write `π = u ϖ ^ e`. If `e` is invertible in `B` and `n = e * d ≠ 0`, the
Kummer ring `A[t]/(t ^ n − π)` maps to the Abhyankar model by sending `t` to `x`.
At every maximal ideal of the model, the maximal ideal of the Kummer ring
generates the maximal ideal of the localization. Thus its ramification
index is one. When the residue extension of `B/A` is algebraic separable, so is
that of each of these localizations over the Kummer ring.

This is the Kummer base-change computation in Abhyankar's lemma for discrete
valuation rings, Stacks Project, Lemma 15.116.4 (Tag 0BRM). The model has already
been identified with the normalization of the root extraction; the results here
measure its ramification over the new base, rather than over `B`.
-/

public section

open Polynomial IsLocalRing

namespace TauCeti

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {π : A} {ϖ u : B} {e d : ℕ}

section Local

variable [IsDomain A] [IsDiscreteValuationRing A]
  [IsDomain B] [IsDiscreteValuationRing B]
  (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hu : IsUnit u)
  (he : IsUnit (e : B)) (hd : d ≠ 0)
  (hπB : algebraMap A B π = u * ϖ ^ e)

variable (M : Ideal (abhyankarModel ϖ u e d)) [M.IsMaximal]

include hϖ hu in
/-- The maximal ideal of the Kummer ring generates the maximal ideal at every maximal
localization of the Abhyankar model. No separability of the residue extension of `B/A`
is needed for this assertion. -/
theorem map_maximalIdeal_abhyankarModelKummerHom :
    letI := standardTameCover_isLocalRing
      ((mem_maximalIdeal π).mpr hπ.not_isUnit) (mul_ne_zero he.neZero_natCast.out hd)
    (maximalIdeal (standardTameCover A π (e * d))).map
      ((algebraMap _ (Localization.AtPrime M)).comp (abhyankarModelKummerHom hπB).toRingHom) =
        maximalIdeal (Localization.AtPrime M) := by
  have hn := mul_ne_zero he.neZero_natCast.out hd
  have := standardTameCover_isLocalRing ((mem_maximalIdeal π).mpr hπ.not_isUnit) hn
  have hmax := (isEisensteinAt_X_pow_sub_C_of_irreducible hπ (Nat.pos_of_ne_zero hn)
    ).eq_span_singleton_of_isMaximal (monic_X_pow_sub_C π hn)
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) AdjoinRoot.adjoinRoot_eq_top
      (maximalIdeal (standardTameCover A π (e * d)))
  rw [hmax]
  simpa only [Ideal.map_span, Set.image_singleton, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, abhyankarModelKummerHom_root] using
    (maximalIdeal_eq_span_abhyankarModelRoot (Localization.AtPrime M) M hϖ hu he hd).symm

include hπ hϖ hu he hd in
/-- The map from the Kummer ring to a maximal localization of the Abhyankar model is local. -/
theorem isLocalHom_abhyankarModelKummerHom :
    letI := standardTameCover_isLocalRing
      ((mem_maximalIdeal π).mpr hπ.not_isUnit) (mul_ne_zero he.neZero_natCast.out hd)
    IsLocalHom ((algebraMap _ (Localization.AtPrime M)).comp
      (abhyankarModelKummerHom (d := d) hπB).toRingHom) := by
  have := standardTameCover_isLocalRing ((mem_maximalIdeal π).mpr hπ.not_isUnit)
    (mul_ne_zero he.neZero_natCast.out hd)
  exact ((local_hom_tfae _).out 3 1).mp
    (map_maximalIdeal_abhyankarModelKummerHom hπ hϖ hu he hd hπB M).le

include hπ hϖ hu he hd in
/-- After adjoining an `e * d`-th root of `π`, every maximal localization of the
Abhyankar model has ramification index one over the Kummer base. -/
theorem ramificationIdx_abhyankarModelKummerHom :
    letI := standardTameCover_isLocalRing
      ((mem_maximalIdeal π).mpr hπ.not_isUnit) (mul_ne_zero he.neZero_natCast.out hd)
    letI := ((algebraMap _ (Localization.AtPrime M)).comp
      (abhyankarModelKummerHom (d := d) hπB).toRingHom).toAlgebra
    (maximalIdeal (Localization.AtPrime M)).ramificationIdx
      (standardTameCover A π (e * d)) = 1 := by
  let R := standardTameCover A π (e * d)
  let S := Localization.AtPrime M
  have := standardTameCover_isLocalRing ((mem_maximalIdeal π).mpr hπ.not_isUnit)
    (mul_ne_zero he.neZero_natCast.out hd)
  let := ((algebraMap _ S).comp (abhyankarModelKummerHom (d := d) hπB).toRingHom).toAlgebra
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    map_maximalIdeal_abhyankarModelKummerHom hπ hϖ hu he hd hπB M
  have : IsLocalHom (algebraMap R S) :=
    isLocalHom_abhyankarModelKummerHom hπ hϖ hu he hd hπB M
  have := isRegularLocalRing_abhyankarModel S M hϖ hu he hd
  have := isDiscreteValuationRing_abhyankarModel S M hϖ hu he hd
  exact IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow
    (by simpa using hmap)

include hπ hϖ hu he hd in
/-- If the original residue extension is algebraic separable, then each maximal localization
of the Abhyankar model has algebraic separable residue extension over the Kummer base. -/
theorem isSeparable_abhyankarModelKummerHom
    [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    letI := standardTameCover_isLocalRing
      ((mem_maximalIdeal π).mpr hπ.not_isUnit) (mul_ne_zero he.neZero_natCast.out hd)
    letI := ((algebraMap _ (Localization.AtPrime M)).comp
      (abhyankarModelKummerHom (d := d) hπB).toRingHom).toAlgebra
    letI := isLocalHom_abhyankarModelKummerHom hπ hϖ hu he hd hπB M
    Algebra.IsSeparable (ResidueField (standardTameCover A π (e * d)))
      (ResidueField (Localization.AtPrime M)) := by
  let R := standardTameCover A π (e * d)
  let S := Localization.AtPrime M
  have he₀ := he.neZero_natCast.out
  have hn := mul_ne_zero he₀ hd
  have := standardTameCover_isLocalRing ((mem_maximalIdeal π).mpr hπ.not_isUnit) hn
  let := ((algebraMap _ S).comp (abhyankarModelKummerHom (d := d) hπB).toRingHom).toAlgebra
  have : IsLocalHom (algebraMap R S) :=
    isLocalHom_abhyankarModelKummerHom hπ hϖ hu he hd hπB M
  have : IsScalarTower A R S := .of_algebraMap_eq fun a ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply A (abhyankarModel ϖ u e d) S]
  -- Finiteness makes every maximal ideal of the model lie over the closed point of `B`.
  obtain ⟨_, hrank⟩ := abhyankarModel_free ϖ u (Nat.pos_of_ne_zero he₀)
    (Nat.pos_of_ne_zero hd)
  have : Module.Finite B (abhyankarModel ϖ u e d) :=
    Module.finite_of_finrank_pos (hrank ▸ Nat.pos_of_ne_zero hn)
  have : M.LiesOver (maximalIdeal B) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under B M)).symm⟩
  have : IsLocalHom (algebraMap B S) := by
    apply ((local_hom_tfae _).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq B (abhyankarModel ϖ u e d) S, ← Ideal.comap_comap,
      ← Ideal.under_def (abhyankarModel ϖ u e d),
      IsLocalization.AtPrime.under_maximalIdeal S M,
      ← Ideal.under_def, ← Ideal.over_def M (maximalIdeal B)]
  have := isSeparable_abhyankarModel_quotient M
    ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hu he hd
  -- Localization at a maximal ideal does not change its residue field.
  let σ := (IsLocalization.AtPrime.equivQuotMaximalIdeal M S).restrictScalars B
  let τ := σ.extendScalarsOfSurjective (R := B) (S := B ⧸ maximalIdeal B)
    Ideal.Quotient.mk_surjective
  have : Algebra.IsSeparable (ResidueField B) (ResidueField S) :=
    (AlgEquiv.Algebra.isSeparable_iff τ).mp inferInstance
  have : IsLocalHom (algebraMap A S) := by
    rw [IsScalarTower.algebraMap_eq A B S]
    infer_instance
  -- Compose with the original residue extension, then enlarge the residue base to that of `R`.
  have : Algebra.IsSeparable (ResidueField A) (ResidueField S) :=
    .trans _ (ResidueField B) _
  have : IsLocalHom ((algebraMap R S).comp (algebraMap A R)) := by
    rw [← IsScalarTower.algebraMap_eq]
    infer_instance
  have : IsLocalHom (algebraMap A R) :=
    isLocalHom_of_comp (algebraMap A R) (algebraMap R S)
  exact Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField R)
    (ResidueField S)

end Local

end TauCeti
