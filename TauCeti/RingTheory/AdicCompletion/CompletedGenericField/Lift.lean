/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Map

/-!
# Extending maps into the completed generic integers

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

private theorem isAdicComplete_maximalIdeal_completedGenericIntegers :
    IsAdicComplete (maximalIdeal (completedGenericIntegers π)) (completedGenericIntegers π) := by
  rw [maximalIdeal_completedGenericIntegers]
  exact isAdicComplete_completedGenericIntegers π

/-- The map from the generic local ring extends to its maximal-ideal completion. -/
noncomputable def completedGenericIntegersLift :
    completedGenericIntegers π →+* completedGenericIntegers π := by
  letI := isAdicComplete_maximalIdeal_completedGenericIntegers π
  letI : Algebra ℤ (genericLocalRing π) := Ring.toIntAlgebra _
  letI : Algebra ℤ (completedGenericIntegers π) := Ring.toIntAlgebra _
  let e := _root_.AdicCompletion.ofAlgEquiv (maximalIdeal (completedGenericIntegers π))
  exact e.symm.toRingEquiv.toRingHom.comp (_root_.AdicCompletion.mapₐ
    (genericLocalRingLift π f hf).toIntAlgHom (genericLocalRingLift_le_comap π f hf)).toRingHom

/-- The completed extension agrees with the map on the generic local ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap_local (a : genericLocalRing π) :
    completedGenericIntegersLift π f hf
      (algebraMap (genericLocalRing π) (completedGenericIntegers π) a) =
        genericLocalRingLift π f hf a := by
  let : Algebra ℤ (genericLocalRing π) := Ring.toIntAlgebra _
  let : Algebra ℤ (completedGenericIntegers π) := Ring.toIntAlgebra _
  have := isAdicComplete_maximalIdeal_completedGenericIntegers π
  let e := _root_.AdicCompletion.ofAlgEquiv (maximalIdeal (completedGenericIntegers π))
  let g := (genericLocalRingLift π f hf).toIntAlgHom
  change e.symm (_root_.AdicCompletion.mapₐ g (genericLocalRingLift_le_comap π f hf)
    (_root_.AdicCompletion.of _ _ a)) = _
  exact (congrArg e.symm (_root_.AdicCompletion.mapₐ_of g
    (genericLocalRingLift_le_comap π f hf) a)).trans
    (_root_.AdicCompletion.ofAlgEquiv_symm_of _ _)

/-- The completed extension agrees with the map on the original affine ring. -/
@[simp]
theorem completedGenericIntegersLift_algebraMap (a : A) :
    completedGenericIntegersLift π f hf (algebraMap A (completedGenericIntegers π) a) = f a := by
  rw [IsScalarTower.algebraMap_apply A (genericLocalRing π) (completedGenericIntegers π),
    completedGenericIntegersLift_algebraMap_local, genericLocalRingLift_algebraMap]

include hf in
private theorem isLocalHom_of_affine_agreement
    (g : completedGenericIntegers π →+* completedGenericIntegers π)
    (hg : g (algebraMap A (completedGenericIntegers π) π) = f π) : IsLocalHom g := by
  apply ((local_hom_tfae _).out 4 1).mp
  rw [maximalIdeal_completedGenericIntegers π, Ideal.span_singleton_le_iff_mem,
    Ideal.mem_comap, hg, ← maximalIdeal_completedGenericIntegers, ← Ideal.mem_comap, hf]
  exact Ideal.mem_span_singleton_self π

/-- The extension preserves the maximal ideal. -/
instance completedGenericIntegersLift_isLocalHom : IsLocalHom
    (completedGenericIntegersLift π f hf) :=
  isLocalHom_of_affine_agreement π f hf _ (completedGenericIntegersLift_algebraMap π f hf π)

/-- The integral extension is uniquely determined by its values on the affine ring among
local ring homomorphisms. -/
theorem completedGenericIntegersLift_unique
    (g : completedGenericIntegers π →+* completedGenericIntegers π) [IsLocalHom g]
    (hg : ∀ a : A, g (algebraMap A (completedGenericIntegers π) a) = f a) :
    g = completedGenericIntegersLift π f hf :=
  completedGenericIntegers_ringHom_ext g _ fun a ↦ by
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
  refine valuation_completedGenericField_hom hπ hπ _ _
    (completedGenericFieldLift_algebraMap π f hf hπ hzero) ?_ x
  rwa [completedGenericIntegersLift_algebraMap]

/-- If the parameter maps to an associate of the original uniformizer, the field extension is
continuous for the valuation topology. -/
theorem continuous_completedGenericFieldLift
    (hassoc : Associated (f π) (algebraMap A (completedGenericIntegers π) π)) :
    Continuous (completedGenericFieldLift π f hf hπ hzero) := by
  let E := completedGenericField π hπ
  let F := completedGenericFieldLift π f hf hπ hzero
  refine (uniformContinuous_of_continuousAt_zero F ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero E ℤᵐ⁰).tendsto_iff
    (Valued.hasBasis_nhds_zero E ℤᵐ⁰), true_and, forall_const]
  intro γ
  refine ⟨γ, fun x hx ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hv := completedGenericFieldLift_valuation π f hf hπ hzero hassoc x
  rwa [((Valued.v : Valuation E ℤᵐ⁰).restrict_inj).mpr hv]

/-- Among field maps preserving the valuation ring, the extension to the completed generic
field is uniquely determined by its values on the affine lift. -/
theorem completedGenericFieldLift_unique
    (g : completedGenericField π hπ →+* completedGenericField π hπ)
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1)
    (hg : ∀ a : A, g (algebraMap A (completedGenericField π hπ) a) =
      algebraMap (completedGenericIntegers π) (completedGenericField π hπ) (f a)) :
    g = completedGenericFieldLift π f hf hπ hzero := by
  have hv := completedGenericField_integers π hπ
  let i := algebraMap (completedGenericIntegers π) (completedGenericField π hπ)
  let j := i.codRestrict (Valued.v : Valuation (completedGenericField π hπ) ℤᵐ⁰).integer
    hv.map_le_one
  have hj : Function.Bijective j := by
    refine ⟨fun x y h ↦ hv.hom_inj (congrArg Subtype.val h), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hv.exists_of_le_one y.property
    exact ⟨x, Subtype.ext hx⟩
  let e := RingEquiv.ofBijective j hj
  let g' : completedGenericIntegers π →+* completedGenericIntegers π :=
    e.symm.toRingHom.comp ((g.comp i).codRestrict _ fun x ↦ hint _ (hv.map_le_one x))
  have heq (x : completedGenericIntegers π) : i (g' x) = g (i x) :=
    congrArg Subtype.val (e.apply_symm_apply ((g.comp i).codRestrict _
      (fun y ↦ hint _ (hv.map_le_one y)) x))
  have hbase (a : A) : g' (algebraMap A (completedGenericIntegers π) a) = f a := by
    apply hv.hom_inj
    rw [heq, ← IsScalarTower.algebraMap_apply A (completedGenericIntegers π)
      (completedGenericField π hπ), hg]
  have : IsLocalHom g' := isLocalHom_of_affine_agreement π f hf _ (hbase π)
  have hrestrict : g' = completedGenericIntegersLift π f hf :=
    completedGenericIntegersLift_unique π f hf g' hbase
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors (completedGenericIntegers π))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, completedGenericFieldLift_algebraMap]
  exact (heq x).symm.trans (congrArg i (DFunLike.congr_fun hrestrict x))

end TauCeti.AdicCompletion
