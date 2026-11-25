/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Basic

import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Valuation.Integers
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Extending maps into the completed generic integers

A map from an affine lift to completed generic integers which contracts the target maximal
ideal to the source special fibre extends through the generic localization and its completion.
If the parameter has nonzero image, it extends further to the completed generic field.

## References

* [N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*](https://arxiv.org/abs/1910.03871v3),
  §3.1.
-/

public section

open IsLocalRing
open scoped WithZero

namespace TauCeti.AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B] {π : A} {π' : B}
  [(Ideal.span {π}).IsPrime] [(Ideal.span {π'}).IsPrime]

/-- Local maps of completed generic rings are determined by their values on the affine ring. -/
theorem completedGenericIntegers_ringHom_ext
    (g h : completedGenericIntegers π →+* completedGenericIntegers π')
    [IsLocalHom g] [IsLocalHom h]
    (hgh : ∀ a : A, g (algebraMap A _ a) = h (algebraMap A _ a)) : g = h := by
  have := isAdicComplete_completedGenericIntegers π'
  have hle (k : completedGenericIntegers π →+* completedGenericIntegers π') [IsLocalHom k] :
      (maximalIdeal (genericLocalRing π)).map (algebraMap _ (completedGenericIntegers π)) ≤
        (Ideal.span {algebraMap B (completedGenericIntegers π') π'}).comap k := by
    rw [← maximalIdeal_completedGenericIntegers, IsLocalRing.maximalIdeal_comap]
    exact IsLocalRing.map_maximalIdeal_le _
  refine _root_.AdicCompletion.ringHom_ext (fg_maximalIdeal_genericLocalRing π) (hle g)
    (hle h) (IsLocalization.ringHom_ext (Ideal.span {π}).primeCompl (RingHom.ext fun a ↦ ?_))
  simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] using hgh a

variable (π) (f : A →+* completedGenericIntegers π')
  (hf : (maximalIdeal (completedGenericIntegers π')).comap f = Ideal.span {π})

/-- A map which contracts the maximal ideal to `(π)` extends to the generic local ring. -/
noncomputable def genericLocalRingLift :
    genericLocalRing π →+* completedGenericIntegers π' :=
  IsLocalization.lift (M := (Ideal.span {π}).primeCompl) (S := genericLocalRing π)
    (g := f) fun s ↦ by
      rw [← notMem_maximalIdeal]
      intro hs
      have hs' : (s : A) ∈ (maximalIdeal (completedGenericIntegers π')).comap f :=
        Ideal.mem_comap.mpr hs
      exact s.property (hf.le hs')

/-- The extension to the generic localization agrees with the original map. -/
@[simp]
theorem genericLocalRingLift_algebraMap (a : A) :
    genericLocalRingLift π f hf (algebraMap A (genericLocalRing π) a) = f a :=
  IsLocalization.lift_eq _ a

private theorem genericLocalRingLift_le_comap :
    maximalIdeal (genericLocalRing π) ≤
      (maximalIdeal (completedGenericIntegers π')).comap
        (genericLocalRingLift π f hf).toIntAlgHom := by
  have hmap : (Ideal.span {π}).map (algebraMap A (genericLocalRing π)) ≤
      (maximalIdeal (completedGenericIntegers π')).comap (genericLocalRingLift π f hf) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    have heq : (genericLocalRingLift π f hf).comp (algebraMap A (genericLocalRing π)) = f :=
      RingHom.ext (genericLocalRingLift_algebraMap π f hf)
    simpa only [heq] using hf.ge
  exact (Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.span {π})).ge.trans hmap

/-- The map from the generic local ring extends to its maximal-ideal completion. -/
noncomputable def completedGenericIntegersLift :
    completedGenericIntegers π →+* completedGenericIntegers π' := by
  letI : Algebra ℤ (genericLocalRing π) := Ring.toIntAlgebra _
  letI : Algebra ℤ (completedGenericIntegers π') := Ring.toIntAlgebra _
  let e := _root_.AdicCompletion.ofAlgEquiv (maximalIdeal (completedGenericIntegers π'))
  exact e.symm.toAlgHom.toRingHom.comp (_root_.AdicCompletion.mapₐ
    (genericLocalRingLift π f hf).toIntAlgHom (genericLocalRingLift_le_comap π f hf)).toRingHom

/-- The completed extension agrees with the map on the generic local ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap_genericLocalRing (a : genericLocalRing π) :
    completedGenericIntegersLift π f hf
      (algebraMap (genericLocalRing π) (completedGenericIntegers π) a) =
        genericLocalRingLift π f hf a := by
  -- Match the integer algebra instances used by `RingHom.toIntAlgHom` in the lift.
  let : Algebra ℤ (genericLocalRing π) := Ring.toIntAlgebra _
  let : Algebra ℤ (completedGenericIntegers π') := Ring.toIntAlgebra _
  simp only [completedGenericIntegersLift, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_toAlgHom, _root_.AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rw [_root_.AdicCompletion.mapₐ_of, _root_.AdicCompletion.ofAlgEquiv_symm_of,
    RingHom.toIntAlgHom_apply]

/-- The completed extension agrees with the map on the original affine ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap (a : A) :
    completedGenericIntegersLift π f hf (algebraMap A (completedGenericIntegers π) a) = f a := by
  rw [IsScalarTower.algebraMap_apply A (genericLocalRing π) (completedGenericIntegers π),
    completedGenericIntegersLift_algebraMap_genericLocalRing, genericLocalRingLift_algebraMap]

include hf in
private theorem isLocalHom_of_affine_agreement
    (g : completedGenericIntegers π →+* completedGenericIntegers π')
    (hg : g (algebraMap A (completedGenericIntegers π) π) = f π) : IsLocalHom g := by
  apply ((local_hom_tfae _).out 4 1).mp
  rw [maximalIdeal_completedGenericIntegers π, Ideal.span_singleton_le_iff_mem,
    Ideal.mem_comap, hg, ← Ideal.mem_comap, hf]
  exact Ideal.mem_span_singleton_self π

/-- The extension preserves the maximal ideal. -/
instance completedGenericIntegersLift_isLocalHom : IsLocalHom
    (completedGenericIntegersLift π f hf) :=
  isLocalHom_of_affine_agreement π f hf _ (completedGenericIntegersLift_algebraMap π f hf π)

/-- The integral extension is uniquely determined by its values on the affine ring among
local ring homomorphisms. -/
theorem completedGenericIntegersLift_unique
    (g : completedGenericIntegers π →+* completedGenericIntegers π') [IsLocalHom g]
    (hg : ∀ a : A, g (algebraMap A (completedGenericIntegers π) a) = f a) :
    g = completedGenericIntegersLift π f hf :=
  completedGenericIntegers_ringHom_ext g _ fun a ↦ by
    rw [hg, completedGenericIntegersLift_algebraMap]

section Frobenius

/-- If the affine map induces the `q`-power operation modulo the maximal ideal, its completed
extension induces the same operation on the entire residue field. -/
theorem residue_completedGenericIntegersLift (f : A →+* completedGenericIntegers π)
    (hf : (maximalIdeal (completedGenericIntegers π)).comap f = Ideal.span {π}) {q : ℕ}
    (hpow : ∀ a : A, residue _ (f a) = residue _ (algebraMap A (completedGenericIntegers π) a) ^ q)
    (x : completedGenericIntegers π) :
    residue _ (completedGenericIntegersLift π f hf x) = residue _ x ^ q := by
  let e := completedGenericResidueEquiv π
  let g := ResidueField.map (completedGenericIntegersLift π f hf)
  have haffine (a : A ⧸ Ideal.span {π}) :
      g (e.symm (algebraMap (A ⧸ Ideal.span {π}) (FractionRing (A ⧸ Ideal.span {π})) a)) =
        e.symm (algebraMap (A ⧸ Ideal.span {π}) (FractionRing (A ⧸ Ideal.span {π})) a) ^ q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← completedGenericResidueEquiv_residue_algebraMap, RingEquiv.symm_apply_apply]
    simpa only [g, ResidueField.map_residue, completedGenericIntegersLift_algebraMap] using hpow a
  have hall (y : FractionRing (A ⧸ Ideal.span {π})) : g (e.symm y) = e.symm y ^ q := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A ⧸ Ideal.span {π}) y
    rw [map_div₀, map_div₀, haffine, haffine, div_pow]
  simpa only [g, RingEquiv.symm_apply_apply, ResidueField.map_residue] using hall (e (residue _ x))

end Frobenius

variable [IsNoetherianRing A] [IsNoetherianRing B]
  (hπ : π ∈ nonZeroDivisors A) (hπ' : π' ∈ nonZeroDivisors B)

variable {π} in
/-- A field map that extends an integral map sending the parameter to an associate of the
target parameter preserves the normalized valuations. -/
theorem valuation_completedGenericField_hom
    (g : completedGenericField π hπ →+* completedGenericField π' hπ')
    (k : completedGenericIntegers π →+* completedGenericIntegers π')
    (hg : ∀ x, g (algebraMap _ _ x) = algebraMap _ _ (k x))
    (hk : Associated (k (algebraMap A (completedGenericIntegers π) π))
      (algebraMap B (completedGenericIntegers π') π'))
    (x : completedGenericField π hπ) : Valued.v (g x) = Valued.v x := by
  let := isRegularLocalRing_completedGenericIntegers π hπ
  let := isDiscreteValuationRing_completedGenericIntegers π hπ
  have hparam : Valued.v (algebraMap (completedGenericIntegers π') (completedGenericField π' hπ')
      (k (algebraMap A (completedGenericIntegers π) π))) =
      Valued.v (algebraMap (completedGenericIntegers π) (completedGenericField π hπ)
        (algebraMap A (completedGenericIntegers π) π)) := by
    obtain ⟨u, hu⟩ := hk
    rw [← IsScalarTower.algebraMap_apply A (completedGenericIntegers π),
      valuation_completedGenericField_algebraMap]
    have h := valuation_completedGenericField_algebraMap π' hπ'
    rwa [IsScalarTower.algebraMap_apply B (completedGenericIntegers π'), ← hu, map_mul, map_mul,
      (completedGenericField_integers π' hπ').valuation_unit, mul_one] at h
  have hval (a : completedGenericIntegers π) :
      Valued.v (g (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) a)) =
        Valued.v (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) a) := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha
      (irreducible_completedGenericIntegers π hπ)
    rw [hg]
    simp only [map_mul, map_pow, (completedGenericField_integers π hπ).valuation_unit,
      (completedGenericField_integers π' hπ').one_of_isUnit (u.isUnit.map k), one_mul, hparam]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := completedGenericIntegers π) x
  rw [map_div₀, map_div₀, map_div₀, hval, hval]

variable (hzero : f π ≠ 0)

/-- If the parameter remains nonzero, the map extends to the completed generic field. -/
noncomputable def completedGenericFieldLift :
    completedGenericField π hπ →+* completedGenericField π' hπ' := by
  letI := isRegularLocalRing_completedGenericIntegers π' hπ'
  letI := isLocalizationAway_completedGenericField π hπ
  apply IsLocalization.Away.lift (algebraMap A (completedGenericIntegers π) π)
    (g := (algebraMap (completedGenericIntegers π') (completedGenericField π' hπ')).comp
      (completedGenericIntegersLift π f hf))
  apply isUnit_iff_ne_zero.mpr
  rw [RingHom.comp_apply, completedGenericIntegersLift_algebraMap,
    ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact hzero

/-- The field extension agrees with the map on the integral completion. -/
@[simp]
theorem completedGenericFieldLift_algebraMap_completedGenericIntegers
    (a : completedGenericIntegers π) :
    completedGenericFieldLift π f hf hπ hπ' hzero
      (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) a) =
        algebraMap (completedGenericIntegers π') (completedGenericField π' hπ')
          (completedGenericIntegersLift π f hf a) := by
  simp [completedGenericFieldLift]

/-- The field extension agrees with the original affine map. -/
@[simp]
theorem completedGenericFieldLift_algebraMap (a : A) :
    completedGenericFieldLift π f hf hπ hπ' hzero (algebraMap A (completedGenericField π hπ) a) =
      algebraMap (completedGenericIntegers π') (completedGenericField π' hπ') (f a) := by
  rw [IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
    (completedGenericField π hπ), completedGenericFieldLift_algebraMap_completedGenericIntegers,
    completedGenericIntegersLift_algebraMap]

/-- The field extension maps the source valuation ring into the target valuation ring. -/
theorem valuation_completedGenericFieldLift_le_one {x : completedGenericField π hπ}
    (hx : Valued.v x ≤ 1) :
    Valued.v (completedGenericFieldLift π f hf hπ hπ' hzero x) ≤ 1 := by
  obtain ⟨a, rfl⟩ := (completedGenericField_integers π hπ).exists_of_le_one hx
  rw [completedGenericFieldLift_algebraMap_completedGenericIntegers]
  exact (completedGenericField_integers π' hπ').map_le_one _

/-- The field extension preserves the normalized valuations when the parameter maps to an
associate of the target uniformizer. -/
theorem valuation_completedGenericFieldLift
    (hassoc : Associated (f π) (algebraMap B (completedGenericIntegers π') π'))
    (x : completedGenericField π hπ) :
    Valued.v (completedGenericFieldLift π f hf hπ hπ' hzero x) = Valued.v x := by
  refine valuation_completedGenericField_hom hπ hπ' _ _
    (completedGenericFieldLift_algebraMap_completedGenericIntegers π f hf hπ hπ' hzero) ?_ x
  rwa [completedGenericIntegersLift_algebraMap]

/-- The field extension is continuous for the valuation topologies. -/
theorem continuous_completedGenericFieldLift :
    Continuous (completedGenericFieldLift π f hf hπ hπ' hzero) := by
  let E := completedGenericField π hπ
  let E' := completedGenericField π' hπ'
  let v : Valuation E ℤᵐ⁰ := Valued.v
  let w : Valuation E' ℤᵐ⁰ := Valued.v
  let F := completedGenericFieldLift π f hf hπ hπ' hzero
  let k := completedGenericIntegersLift π f hf
  let i := algebraMap (completedGenericIntegers π) E
  let p := algebraMap A (completedGenericIntegers π) π
  have hv := completedGenericField_integers π hπ
  have hw := completedGenericField_integers π' hπ'
  have hp : w (F (i p)) < 1 := by
    have hmem : p ∈ maximalIdeal (completedGenericIntegers π) := by
      rw [maximalIdeal_completedGenericIntegers]
      exact Ideal.mem_span_singleton_self _
    have hk := IsLocalRing.map_maximalIdeal_le k (Ideal.mem_map_of_mem k hmem)
    rw [completedGenericFieldLift_algebraMap_completedGenericIntegers]
    exact lt_of_le_of_ne (hw.map_le_one _) (fun h ↦
      (mem_maximalIdeal _).mp hk (hw.isUnit_iff_valuation_eq_one.mpr h))
  refine (uniformContinuous_of_continuousAt_zero F ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero E ℤᵐ⁰).tendsto_iff
    (Valued.hasBasis_nhds_zero E' ℤᵐ⁰), true_and, forall_const]
  intro γ
  -- A sufficiently high power of the parameter maps inside the target ball. Use that power
  -- as the source radius so every element in the source ball is an integral multiple of it.
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (w : E' →*₀ ℤᵐ⁰))) γ)
  have hne : v.restrict (i (p ^ n)) ≠ 0 := by
    rw [map_pow, map_pow]
    exact pow_ne_zero n fun h ↦ (hv.valuation_irreducible_pos
      (irreducible_completedGenericIntegers π hπ)).ne' (v.restrict_eq_zero_iff.mp h)
  refine ⟨Units.mk0 _ hne, fun x hx ↦ ?_⟩
  rw [Set.mem_ofPred_eq, Units.val_mk0, v.restrict_lt_iff] at hx
  obtain ⟨a, rfl⟩ := hv.exists_of_le_one (hx.le.trans (hv.map_le_one _))
  obtain ⟨b, rfl⟩ := hv.le_iff_dvd.mp hx.le
  rw [Set.mem_ofPred_eq, w.restrict_lt_iff_lt_embedding, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow]
  refine (mul_le_of_le_one_right zero_le ?_).trans_lt hn
  rw [completedGenericFieldLift_algebraMap_completedGenericIntegers]
  exact hw.map_le_one (k b)

variable {π} in
/-- A map preserving the valuation rings restricts to a map of the integral completions. -/
private noncomputable def completedGenericFieldRestrict
    (g : completedGenericField π hπ →+* completedGenericField π' hπ')
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1) :
    completedGenericIntegers π →+* completedGenericIntegers π' :=
  (completedGenericField_integers π' hπ').equivInteger.symm.toRingHom.comp
    ((g.comp (algebraMap (completedGenericIntegers π) (completedGenericField π hπ))).codRestrict
      _ fun x ↦ hint _ ((completedGenericField_integers π hπ).map_le_one x))

variable {π} in
private theorem completedGenericFieldRestrict_algebraMap
    (g : completedGenericField π hπ →+* completedGenericField π' hπ')
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1) (x : completedGenericIntegers π) :
    algebraMap (completedGenericIntegers π') (completedGenericField π' hπ')
        (completedGenericFieldRestrict hπ hπ' g hint x) =
      g (algebraMap (completedGenericIntegers π) (completedGenericField π hπ) x) := by
  simp only [completedGenericFieldRestrict, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Valuation.Integers.algebraMap_equivInteger_symm_apply]
  exact (RingHom.codRestrict_apply _ _ _ x).trans (RingHom.comp_apply _ _ x)

/-- Among field maps preserving the valuation ring, the extension to the completed generic
field is uniquely determined by its values on the affine lift. -/
theorem completedGenericFieldLift_unique
    (g : completedGenericField π hπ →+* completedGenericField π' hπ')
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1)
    (hg : ∀ a : A, g (algebraMap A (completedGenericField π hπ) a) =
      algebraMap (completedGenericIntegers π') (completedGenericField π' hπ') (f a)) :
    g = completedGenericFieldLift π f hf hπ hπ' hzero := by
  let g' := completedGenericFieldRestrict hπ hπ' g hint
  have hbase (a : A) : g' (algebraMap A (completedGenericIntegers π) a) = f a := by
    apply (completedGenericField_integers π' hπ').hom_inj
    rw [completedGenericFieldRestrict_algebraMap, ← IsScalarTower.algebraMap_apply A
      (completedGenericIntegers π), hg]
  have : IsLocalHom g' := isLocalHom_of_affine_agreement π f hf _ (hbase π)
  have hrestrict : g' = completedGenericIntegersLift π f hf :=
    completedGenericIntegersLift_unique π f hf g' hbase
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors (completedGenericIntegers π))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, completedGenericFieldLift_algebraMap_completedGenericIntegers]
  rw [← completedGenericFieldRestrict_algebraMap hπ hπ' g hint, ← hrestrict]

end TauCeti.AdicCompletion
