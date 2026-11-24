/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Basic

import TauCeti.RingTheory.AdicCompletion.AlgHom
import Mathlib.RingTheory.AdicCompletion.RingHom
import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# Maps of the completed generic field

A map from an affine lift to its completed generic integers which contracts the maximal ideal
to the special fibre extends through the generic localization and its completion. If the
parameter has nonzero image, it extends further to the completed generic field.

## References

* [N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*](https://arxiv.org/abs/1910.03871v3),
  §3.1.
-/

public section

open IsLocalRing
open scoped WithZero

namespace TauCeti.AdicCompletion

variable {A : Type*} [CommRing A] (π : A) [(Ideal.span {π}).IsPrime]
  (f : A →+* completedGenericIntegers π)
  (hf : (maximalIdeal (completedGenericIntegers π)).comap f = Ideal.span {π})

/-- A map which contracts the maximal ideal to `(π)` extends to the generic local ring. -/
noncomputable def genericLocalRingLift :
    genericLocalRing π →+* completedGenericIntegers π :=
  IsLocalization.lift (M := (Ideal.span {π}).primeCompl) (S := genericLocalRing π)
    (g := f) fun s ↦ by
      rw [← notMem_maximalIdeal]
      intro hs
      have hs' : (s : A) ∈ (maximalIdeal (completedGenericIntegers π)).comap f :=
        Ideal.mem_comap.mpr hs
      exact s.property (hf.le hs')

/-- The extension to the generic localization agrees with the original map. -/
@[simp]
theorem genericLocalRingLift_algebraMap (a : A) :
    genericLocalRingLift π f hf (algebraMap A (genericLocalRing π) a) = f a :=
  IsLocalization.lift_eq _ a

private theorem genericLocalRingLift_le_comap :
    maximalIdeal (genericLocalRing π) ≤
      (maximalIdeal (completedGenericIntegers π)).comap (genericLocalRingLift π f hf) := by
  have hmap : (Ideal.span {π}).map (algebraMap A (genericLocalRing π)) ≤
      (maximalIdeal (completedGenericIntegers π)).comap (genericLocalRingLift π f hf) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    have heq : (genericLocalRingLift π f hf).comp (algebraMap A (genericLocalRing π)) = f :=
      RingHom.ext (genericLocalRingLift_algebraMap π f hf)
    simpa only [heq] using hf.ge
  exact (Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.span {π})).ge.trans hmap

private noncomputable def genericLocalRingLiftMod (n : ℕ) :
    completedGenericIntegers π →+*
      completedGenericIntegers π ⧸ maximalIdeal (completedGenericIntegers π) ^ n :=
  (Ideal.quotientMap _ (genericLocalRingLift π f hf)
    ((Ideal.pow_right_mono (genericLocalRingLift_le_comap π f hf) n).trans
      (Ideal.le_comap_pow _ n))).comp
    (_root_.AdicCompletion.evalₐ (maximalIdeal (genericLocalRing π)) n).toRingHom

private theorem genericLocalRingLiftMod_compatible {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal (completedGenericIntegers π)) hle).comp
      (genericLocalRingLiftMod π f hf n) = genericLocalRingLiftMod π f hf m := by
  ext x
  simp only [genericLocalRingLiftMod, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ← _root_.AdicCompletion.factor_evalₐ hle x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (maximalIdeal (genericLocalRing π)) n x)
  simp [← hy]

/-- The map from the generic local ring extends to its maximal-ideal completion. -/
noncomputable def completedGenericIntegersLift :
    completedGenericIntegers π →+* completedGenericIntegers π := by
  letI := isAdicComplete_maximalIdeal_completedGenericIntegers π
  exact _root_.IsAdicComplete.liftRingHom (maximalIdeal (completedGenericIntegers π))
    (genericLocalRingLiftMod π f hf) (genericLocalRingLiftMod_compatible π f hf)

/-- The completed extension agrees with the map on the generic local ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap_local (a : genericLocalRing π) :
    completedGenericIntegersLift π f hf
      (algebraMap (genericLocalRing π) (completedGenericIntegers π) a) =
        genericLocalRingLift π f hf a := by
  have := isAdicComplete_maximalIdeal_completedGenericIntegers π
  apply congrFun (IsHausdorff.funext' (maximalIdeal (completedGenericIntegers π))
    (f := fun x ↦ completedGenericIntegersLift π f hf
      (algebraMap (genericLocalRing π) (completedGenericIntegers π) x))
    (g := genericLocalRingLift π f hf) ?_) a
  intro n x
  simp [completedGenericIntegersLift, genericLocalRingLiftMod,
    _root_.AdicCompletion.algebraMap_apply]

/-- The completed extension agrees with the map on the original affine ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap (a : A) :
    completedGenericIntegersLift π f hf (algebraMap A (completedGenericIntegers π) a) = f a := by
  rw [IsScalarTower.algebraMap_apply A (genericLocalRing π) (completedGenericIntegers π),
    completedGenericIntegersLift_algebraMap_local, genericLocalRingLift_algebraMap]

/-- The extension preserves the maximal ideal. -/
instance completedGenericIntegersLift_isLocalHom : IsLocalHom
    (completedGenericIntegersLift π f hf) := by
  apply ((local_hom_tfae _).out 4 1).mp
  intro x hx
  have hx' : x ∈ Ideal.span {algebraMap A (completedGenericIntegers π) π} :=
    (maximalIdeal_completedGenericIntegers π).le hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx'
  rw [Ideal.mem_comap, map_mul, completedGenericIntegersLift_algebraMap]
  exact Ideal.mul_mem_right _ _ (hf.ge (Ideal.subset_span (Set.mem_singleton π)))

/-- Two local maps from the integral completion agree if they agree on the affine ring. -/
theorem completedGenericIntegers_ringHom_ext
    (g h : completedGenericIntegers π →+* completedGenericIntegers π)
    [IsLocalHom g] [IsLocalHom h]
    (hgh : ∀ a : A, g (algebraMap A (completedGenericIntegers π) a) =
      h (algebraMap A (completedGenericIntegers π) a)) : g = h := by
  have := isAdicComplete_maximalIdeal_completedGenericIntegers π
  have hfg := fg_maximalIdeal_genericLocalRing π
  have hlocal : g.comp (algebraMap (genericLocalRing π) (completedGenericIntegers π)) =
      h.comp (algebraMap (genericLocalRing π) (completedGenericIntegers π)) := by
    apply IsLocalization.ringHom_ext (M := (Ideal.span {π}).primeCompl)
    apply RingHom.ext
    intro a
    simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] using hgh a
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (maximalIdeal (completedGenericIntegers π))
  intro n x
  obtain ⟨y, hy⟩ := _root_.AdicCompletion.exists_sub_algebraMap_mem_map_pow
    hfg n x
  have hxy : x - algebraMap (genericLocalRing π) (completedGenericIntegers π) y ∈
      maximalIdeal (completedGenericIntegers π) ^ n := by
    simpa only [Ideal.map_pow, ← _root_.AdicCompletion.maximalIdeal_eq_map_of_fg
      hfg] using hy
  have hmaps (k : completedGenericIntegers π →+* completedGenericIntegers π) [IsLocalHom k] :
      k (x - algebraMap (genericLocalRing π) (completedGenericIntegers π) y) ∈
        maximalIdeal (completedGenericIntegers π) ^ n := by
    apply Ideal.pow_right_mono (map_maximalIdeal_le k) n
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem k hxy
  apply Ideal.Quotient.eq.mpr
  have heq : g (algebraMap (genericLocalRing π) (completedGenericIntegers π) y) =
      h (algebraMap (genericLocalRing π) (completedGenericIntegers π) y) :=
    DFunLike.congr_fun hlocal y
  simpa only [map_sub, heq, sub_sub_sub_cancel_right] using
    (maximalIdeal (completedGenericIntegers π) ^ n).sub_mem (hmaps g) (hmaps h)

/-- The integral extension is uniquely determined by its values on the affine ring among
local ring homomorphisms. -/
theorem completedGenericIntegersLift_unique
    (g : completedGenericIntegers π →+* completedGenericIntegers π) [IsLocalHom g]
    (hg : ∀ a : A, g (algebraMap A (completedGenericIntegers π) a) = f a) :
    g = completedGenericIntegersLift π f hf :=
  completedGenericIntegers_ringHom_ext π g _ fun a ↦ by
    rw [hg, completedGenericIntegersLift_algebraMap]

variable [IsNoetherianRing A] (hπ : π ∈ nonZeroDivisors A) (hzero : f π ≠ 0)

/-- If the parameter remains nonzero, the map extends to the completed generic field. -/
noncomputable def completedGenericFieldLift :
    completedGenericField π hπ →+* completedGenericField π hπ := by
  letI := isRegularLocalRing_completedGenericIntegers π hπ
  letI := isLocalizationAway_completedGenericField π hπ
  apply IsLocalization.Away.lift (algebraMap A (completedGenericIntegers π) π)
    (g := (algebraMap (completedGenericIntegers π) (completedGenericField π hπ)).comp
      (completedGenericIntegersLift π f hf))
  apply isUnit_iff_ne_zero.mpr
  rw [RingHom.comp_apply, completedGenericIntegersLift_algebraMap,
    ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact hzero

/-- The field extension agrees with the map on the integral completion. -/
@[simp]
theorem completedGenericFieldLift_algebraMap (a : completedGenericIntegers π) :
    completedGenericFieldLift π f hf hπ hzero
      (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) a) =
        algebraMap (completedGenericIntegers π) (completedGenericField π hπ)
          (completedGenericIntegersLift π f hf a) := by
  simp [completedGenericFieldLift]

/-- The field extension agrees with the original affine map. -/
@[simp]
theorem completedGenericFieldLift_algebraMap_affine (a : A) :
    completedGenericFieldLift π f hf hπ hzero (algebraMap A (completedGenericField π hπ) a) =
      algebraMap (completedGenericIntegers π) (completedGenericField π hπ) (f a) := by
  rw [IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
    (completedGenericField π hπ), completedGenericFieldLift_algebraMap,
    completedGenericIntegersLift_algebraMap]

/-- The field extension preserves the normalized valuation when the parameter maps to an
associate of the original uniformizer. -/
theorem completedGenericFieldLift_valuation
    (hassoc : Associated (f π) (algebraMap A (completedGenericIntegers π) π))
    (x : completedGenericField π hπ) :
    Valued.v (completedGenericFieldLift π f hf hπ hzero x) = Valued.v x := by
  let := isRegularLocalRing_completedGenericIntegers π hπ
  let := isDiscreteValuationRing_completedGenericIntegers π hπ
  have hv := completedGenericField_integers π hπ
  have hunit (u : (completedGenericIntegers π)ˣ) :
      Valued.v (algebraMap (completedGenericIntegers π) (completedGenericField π hπ)
        (completedGenericIntegersLift π f hf u)) = 1 :=
    hv.one_of_isUnit (u.isUnit.map _)
  have hparam : Valued.v (algebraMap (completedGenericIntegers π)
      (completedGenericField π hπ) (f π)) =
        Valued.v (algebraMap A (completedGenericField π hπ) π) := by
    obtain ⟨u, hu⟩ := hassoc
    have hvu := hv.valuation_unit u
    rw [IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
      (completedGenericField π hπ), ← hu, map_mul, map_mul, hvu, mul_one]
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (irreducible_completedGenericIntegers π hπ) hx
  simp only [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
    completedGenericFieldLift_algebraMap, completedGenericIntegersLift_algebraMap,
    hunit, hv.valuation_unit, one_mul]
  rw [← IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
    (completedGenericField π hπ), hparam]

/-- Among field maps preserving the valuation ring, the extension to the completed generic
field is uniquely determined by its values on the affine lift. -/
theorem completedGenericFieldLift_unique
    (g : completedGenericField π hπ →+* completedGenericField π hπ)
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1)
    (hg : ∀ a : A, g (algebraMap A (completedGenericField π hπ) a) =
      algebraMap (completedGenericIntegers π) (completedGenericField π hπ) (f a)) :
    g = completedGenericFieldLift π f hf hπ hzero := by
  have hv := completedGenericField_integers π hπ
  let e := completedGenericIntegersEquivInteger π hπ
  let g' : completedGenericIntegers π →+* completedGenericIntegers π :=
    e.symm.toRingHom.comp ((g.comp (algebraMap (completedGenericIntegers π)
      (completedGenericField π hπ))).codRestrict _ fun x ↦ hint _ (hv.map_le_one x))
  have heq (x : completedGenericIntegers π) :
      algebraMap (completedGenericIntegers π) (completedGenericField π hπ) (g' x) =
        g (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) x) := by
    rw [← completedGenericIntegersEquivInteger_apply π hπ]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hbase (a : A) : g' (algebraMap A (completedGenericIntegers π) a) = f a := by
    apply hv.hom_inj
    rw [heq, ← IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
      (completedGenericField π hπ), hg]
  have : IsLocalHom g' := by
    apply ((local_hom_tfae _).out 4 1).mp
    apply (maximalIdeal_completedGenericIntegers π).le.trans
    rw [Ideal.span_singleton_le_iff_mem]
    apply Ideal.mem_comap.mpr
    rw [hbase]
    exact hf.ge (Ideal.subset_span rfl)
  have hrestrict : g' = completedGenericIntegersLift π f hf :=
    completedGenericIntegersLift_unique π f hf g' hbase
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors (completedGenericIntegers π))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, completedGenericFieldLift_algebraMap, ← heq, hrestrict]

end TauCeti.AdicCompletion
