/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.MvPolynomial.Localization
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.Spectrum.Prime.GenericFreeness

/-!
# Generic étaleness and separability of function fields

A dominant morphism of integral schemes locally of finite type is étale on an open
neighbourhood of the generic point exactly when its extension of function fields is separable.
This uses the formal unramifiedness criterion in `Morphisms/FormallyUnramified.lean` and
`AlgebraicGeometry.Scheme.Hom.etaleAt_iff_stalkMap` after obtaining finite presentation
near the generic point by generic freeness.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

open scoped nonZeroDivisors

/-- A surjection from a finite-type algebra over a domain with torsion kernel
becomes an isomorphism after inverting a nonzero base element. -/
private theorem exists_bijective_awayMap_of_torsion_ker {R T S : Type u}
    [CommRing R] [IsDomain R] [CommRing T] [Algebra R T] [Algebra.FiniteType R T]
    [CommRing S] [Algebra R S] (π : T →ₐ[R] S) (hπ : Function.Surjective π)
    (htorsion : ∀ t, π t = 0 → ∃ b : R, b ≠ 0 ∧ b • t = 0) :
    ∃ a : R, a ≠ 0 ∧ Function.Bijective (Localization.awayMap π.toRingHom (algebraMap R T a)) := by
  obtain ⟨_, ⟨a, rfl⟩, ha, hfree⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).mem_nhds_iff.mp
      (Module.freeLocus_mem_nhds_bot (A := R) (B := T) T)
  have ha₀ : a ≠ 0 := by simpa using ha
  have hreg := powers_le_nonZeroDivisors_of_noZeroDivisors ha₀
  have : IsDomain (Localization.Away a) := IsLocalization.isDomain_localization hreg
  have : Module.Flat (Localization.Away a) (LocalizedModule.Away a T) := by
    apply Module.flat_of_localized_maximal
    intro m _
    have hm : (⟨m, inferInstance⟩ : PrimeSpectrum (Localization.Away a)) ∈
        Module.freeLocus (Localization.Away a) (LocalizedModule.Away a T) := by
      rw [Module.freeLocus_localization]
      apply hfree
      change PrimeSpectrum.comap (algebraMap R (Localization.Away a)) ⟨m, inferInstance⟩ ∈
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R))
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact ⟨⟨m, inferInstance⟩, rfl⟩
    have := Module.mem_freeLocus.mp hm
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime m) m.primeCompl _).mp
      inferInstance
  let l := LocalizedModule.mkLinearMap (Submonoid.powers a) T
  refine ⟨a, ha₀, Localization.awayMap_injective_iff.mpr ?_,
    Localization.awayMap_surjective_iff.mpr ?_⟩
  · intro t ht
    obtain ⟨b, hb, hbt⟩ := htorsion t ht
    have hb' : algebraMap R (Localization.Away a) b ≠ 0 := by
      simpa only [map_zero] using (IsLocalization.injective (Localization.Away a)
        hreg).ne hb
    have hl : l t = 0 := by
      apply (Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hb'))
      change algebraMap R (Localization.Away a) b • l t =
        algebraMap R (Localization.Away a) b • 0
      rw [algebraMap_smul, ← l.map_smul, hbt, map_zero, smul_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (.powers a) l).mp
      (hl.trans l.map_zero.symm)
    change (a ^ n : R) • t = (a ^ n : R) • 0 at hn
    exact ⟨n, by simpa [Algebra.smul_def] using hn⟩
  · intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x, 0, by simp⟩

/-- A finite-type algebra over a domain becomes finitely presented after inverting a nonzero
base element. Choose finitely many relations generating the kernel up to base torsion, and
apply generic freeness to the algebra defined by those relations. -/
private theorem exists_finitePresentation_away_of_finiteType {R S : Type u}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ a : R, a ≠ 0 ∧ Algebra.FinitePresentation R (Localization.Away (algebraMap R S a)) := by
  classical
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let P := MvPolynomial (Fin n) R
  let K := FractionRing R
  let Pₖ := MvPolynomial (Fin n) K
  let M := (R⁰).map (MvPolynomial.C (σ := Fin n))
  let : Algebra P Pₖ := MvPolynomial.algebraMvPolynomial
  let j : P →ₗ[P] Pₖ := Algebra.linearMap P Pₖ
  have hj : Function.Injective j :=
    MvPolynomial.map_injective _ (IsFractionRing.injective R K)
  have : IsLocalization M Pₖ := MvPolynomial.isLocalization ..
  obtain ⟨s, hs, hrel⟩ := Submodule.exists_finset_smul_mem_span_of_fg_span_image (f := j) hj M
    (N := RingHom.ker φ.toRingHom) (IsNoetherian.noetherian (R := Pₖ) _)
  let I : Ideal P := Ideal.span (s : Set P)
  let T := P ⧸ I
  let π : T →ₐ[R] S := Ideal.Quotient.liftₐ I φ (Ideal.span_le.mpr hs)
  have hπ : Function.Surjective π := fun y ↦
    let ⟨x, hx⟩ := hφ y
    ⟨Ideal.Quotient.mk I x, hx⟩
  have : Algebra.FinitePresentation R T := Algebra.FinitePresentation.quotient ⟨s, rfl⟩
  have htorsion (t : T) (ht : π t = 0) : ∃ b : R, b ≠ 0 ∧ b • t = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨_, ⟨b, hb, rfl⟩, hx⟩ := hrel x ht
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    change b • (Ideal.Quotient.mkₐ R I) x = 0
    rw [← map_smul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change b • x ∈ I
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    exact hx
  obtain ⟨a, ha₀, hmap⟩ := exists_bijective_awayMap_of_torsion_ker π hπ htorsion
  let a' := algebraMap R T a
  have hfp : ((algebraMap T (Localization.Away a')).comp (algebraMap R T)).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation a')).comp
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have ha' : π a' = algebraMap R S a := π.commutes a
  refine ⟨a, ha₀, ?_⟩
  rw [← ha']
  apply RingHom.finitePresentation_algebraMap.mp
  convert (RingHom.FinitePresentation.of_bijective hmap).comp hfp using 1
  ext r
  have hcomm : (Localization.awayMap π.toRingHom a').comp (algebraMap T (Localization.Away a')) =
      (algebraMap S _).comp π.toRingHom := IsLocalization.map_comp _
  change algebraMap S _ (algebraMap R S r) =
    ((Localization.awayMap π.toRingHom a').comp (algebraMap T (Localization.Away a')))
      (algebraMap R T r)
  rw [hcomm, RingHom.comp_apply]
  exact congrArg (algebraMap S _) (π.commutes r).symm

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]

/-- A dominant morphism of integral schemes locally of finite type is étale on an open
neighbourhood of the generic point precisely when its extension of function fields is separable. -/
theorem etaleAt_genericPoint_iff_isSeparable_functionField [LocallyOfFiniteType f] :
    (∃ U : X.Opens, genericPoint X ∈ U ∧ Etale (U.ι ≫ f)) ↔
      letI := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField := by
  rw [← f.formallyUnramified_stalkMap_genericPoint_iff_isSeparable_functionField]
  refine ⟨fun ⟨U, hxU, _⟩ ↦ f.formallyUnramified_stalkMap_of_isOpenImmersion_comp
    U.ι ⟨genericPoint X, hxU⟩, fun hfu ↦ ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (genericPoint X))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  obtain ⟨a, ha, hfp⟩ :=
    TauCeti.exists_finitePresentation_away_of_finiteType (R := Γ(Y, U)) (S := Γ(X, V))
  have haV : algebraMap Γ(Y, U) Γ(X, V) a ≠ 0 := by
    rw [RingHom.algebraMap_toAlgebra]
    simpa only [map_zero] using (f.appLE_injective_of_isDominant U V hVU).ne ha
  let r := algebraMap Γ(Y, U) Γ(X, V) a
  let W := X.basicOpen r
  have hxW : genericPoint X ∈ W := by
    rw [hV.mem_basicOpen_iff_notMem_primeIdealOf ⟨_, hxV⟩, hV.primeIdealOf_genericPoint,
      genericPoint_eq_bot_of_affine]
    exact haV
  have hWV : W ≤ f ⁻¹ᵁ U := (X.basicOpen_le r).trans hVU
  have : LocallyOfFinitePresentation (W.ι ≫ f) := by
    rw [← f.resLE_comp_ι hWV]
    have := HasRingHomProperty.resLE_basicOpen @LocallyOfFinitePresentation hU hV hVU r
      (RingHom.finitePresentation_algebraMap.mpr hfp)
    infer_instance
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [f.genericPoint_eq_of_isDominant]
    exact Field.toIsField Y.functionField
  let x : W := ⟨_, hxW⟩
  have hflat := RingHom.Flat.of_isField hfield (f.stalkMap (genericPoint X)).hom
  obtain ⟨O, hxO, hO⟩ := ((W.ι ≫ f).etaleAt_iff_stalkMap x).mpr
    ⟨(RingHom.Flat.respectsIso.stalkMap_comp_isOpenImmersion_iff W.ι f x).mpr hflat,
     (RingHom.FormallyUnramified.respectsIso.stalkMap_comp_isOpenImmersion_iff W.ι f x).mpr hfu⟩
  refine ⟨W.ι ''ᵁ O, ⟨x, hxO, rfl⟩, ?_⟩
  rw [← W.ι.isoImage_inv_ι O, Category.assoc, Category.assoc]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
