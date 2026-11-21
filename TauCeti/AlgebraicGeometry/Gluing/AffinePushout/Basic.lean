/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.LocalRing.Pullback

import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.RingTheory.FiberProduct.Basic

/-!
# The affine square for finite pinching

Given a surjection `B → C` and a ring map `D → C`, the spectrum of the pullback ring
`B ×_C D` is the topological pushout. The square of affine schemes is
cartesian and the map from `Spec D` is a closed immersion. The map from `Spec B` is finite
when `D → C` is finite.
These are the topology and morphism properties of the affine Ferrand construction.

See [Ferrand, *Conducteur, descente et pincement*][ferrand], Theorem 5.1, and the Stacks Project,
[Lemma 15.6.2][stacks-0B7J].

[ferrand]: https://www.numdam.org/articles/10.24033/bsmf.2455/
[stacks-0B7J]: https://stacks.math.columbia.edu/tag/0B7J
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open PrimeSpectrum Function

universe u

namespace RingHom

variable {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
variable (p : B →+* C) (q : D →+* C)

/-- The square of affine schemes associated to a ring pullback along a surjection is cartesian. -/
theorem isPullback_spec_pullback (hp : Surjective p) :
    IsPullback (Spec.map (CommRingCat.ofHom p)) (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)))
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (p.isPushout_pullback q hp)

/-- The second projection of a ring pullback along a surjection induces a closed immersion. -/
theorem isClosedImmersion_spec_pullbackSnd (hp : Surjective p) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))) :=
  IsClosedImmersion.spec_of_surjective _ (p.surjective_pullbackSnd_of_surjective q hp)

/-- The map from the spectrum of the original ring to the affine pinch is finite. -/
theorem isFinite_spec_pullbackFst (hp : Surjective p) (hq : q.Finite) :
    IsFinite (Spec.map (CommRingCat.ofHom (p.pullbackFst q))) :=
  (IsFinite.SpecMap_iff _).mpr (p.finite_pullbackFst_of_surjective q hp hq)

private theorem isIso_spec_pullbackFst_restrict_basicOpen {t : p.pullback q}
    (ht : t ∈ RingHom.ker (p.pullbackSnd q)) :
    IsIso (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ∣_ PrimeSpectrum.basicOpen t) :=
  ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (p.pullbackFst q)) t)).mpr
    (isIso_SpecMap_iff.mpr (p.bijective_awayMap_pullbackFst q ht))

/-- The map from the first spectrum is an isomorphism over the complement of the closed
locus of the second projection. The domain is the preimage of that complement. -/
theorem isIso_spec_pullbackFst_restrict_compl :
    IsIso (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ∣_
      (⟨(zeroLocus (RingHom.ker (p.pullbackSnd q))).compl,
        (isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (CommRingCat.of (p.pullback q))).Opens)) := by
  let f := Spec.map (CommRingCat.ofHom (p.pullbackFst q))
  let U : RingHom.ker (p.pullbackSnd q) → (Spec (CommRingCat.of (p.pullback q))).Opens :=
    fun t ↦ PrimeSpectrum.basicOpen t.val
  have hU : (⨆ t, U t) =
      (⟨(zeroLocus (RingHom.ker (p.pullbackSnd q))).compl,
        (isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (CommRingCat.of (p.pullback q))).Opens) := by
    apply TopologicalSpace.Opens.ext
    ext x
    rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
    let x' : PrimeSpectrum (p.pullback q) := x
    -- Use prime-spectrum membership to describe the two opens of the affine scheme.
    change (∃ t : RingHom.ker (p.pullbackSnd q), x' ∈ PrimeSpectrum.basicOpen t.val) ↔
      x' ∉ zeroLocus (RingHom.ker (p.pullbackSnd q))
    constructor
    · rintro ⟨t, ht⟩ h
      exact (mem_basicOpen _ x').mp ht ((mem_zeroLocus _ _).mp h t.property)
    · intro h
      obtain ⟨t, ht, htx⟩ := Set.not_subset.mp (fun hs ↦ h ((mem_zeroLocus x' _).mpr hs))
      exact ⟨⟨t, ht⟩, (mem_basicOpen _ x').mpr htx⟩
  have h : IsIso (f ∣_ iSup U) :=
    f.isIso_morphismRestrict_iSup U fun t ↦ p.isIso_spec_pullbackFst_restrict_basicOpen q t.property
  exact hU ▸ h

private theorem existsUnique_comap_pullbackFst_of_notMem {t : p.pullback q}
    (ht : t ∈ RingHom.ker (p.pullbackSnd q)) {x : PrimeSpectrum (p.pullback q)}
    (hx : t ∉ x.asIdeal) :
    ∃! y : PrimeSpectrum B, comap (p.pullbackFst q) y = x := by
  let f := Spec.map (CommRingCat.ofHom (p.pullbackFst q))
  let U := PrimeSpectrum.basicOpen t
  have hxU : x ∈ U := (mem_basicOpen t x).mpr hx
  have : IsIso (f ∣_ U) := p.isIso_spec_pullbackFst_restrict_basicOpen q ht
  have hf := (Scheme.homeoOfIso (asIso (f ∣_ U))).bijective
  obtain ⟨y, hy⟩ := hf.surjective ⟨x, hxU⟩
  refine ⟨y.val, ?_, fun y' hy' ↦ ?_⟩
  · exact (morphismRestrict_base_coe f U y).symm.trans (congrArg Subtype.val hy)
  · have hy'U : y' ∈ f ⁻¹ᵁ U := by
      refine (Scheme.Hom.mem_preimage f).mpr ?_
      exact show comap (p.pullbackFst q) y' ∈ U from by rw [hy']; exact hxU
    have hy'' : (f ∣_ U) ⟨y', hy'U⟩ = ⟨x, hxU⟩ :=
      Subtype.ext ((morphismRestrict_base_coe f U ⟨y', hy'U⟩).trans hy')
    exact congrArg Subtype.val (hf.injective (hy''.trans hy.symm))

private theorem surjective_sumElim_comap_pullback (hp : Surjective p) :
    Surjective (Sum.elim (comap (p.pullbackFst q)) (comap (p.pullbackSnd q))) := by
  intro x
  by_cases hx : RingHom.ker (p.pullbackSnd q) ≤ x.asIdeal
  · obtain ⟨y, rfl⟩ : x ∈ Set.range (comap (p.pullbackSnd q)) := by
      rw [range_comap_of_surjective _ _ (p.surjective_pullbackSnd_of_surjective q hp),
        mem_zeroLocus]
      exact hx
    exact ⟨Sum.inr y, rfl⟩
  · obtain ⟨t, ht, htx⟩ := Set.not_subset.mp hx
    obtain ⟨y, hy, -⟩ := p.existsUnique_comap_pullbackFst_of_notMem q ht htx
    exact ⟨Sum.inl y, hy⟩

private theorem exists_comap_eq_of_comap_pullbackFst_eq_comap_pullbackSnd (hp : Surjective p)
    {x : PrimeSpectrum B} {y : PrimeSpectrum D}
    (h : comap (p.pullbackFst q) x = comap (p.pullbackSnd q) y) :
    ∃ z : PrimeSpectrum C, comap p z = x ∧ comap q z = y := by
  have hx : RingHom.ker p ≤ x.asIdeal := by
    rw [← p.map_pullbackFst_ker_pullbackSnd_eq q, Ideal.map_le_iff_le_comap]
    rw [← comap_asIdeal, h, comap_asIdeal]
    exact fun a ha ↦ by rw [Ideal.mem_comap, RingHom.mem_ker.mp ha]; exact Ideal.zero_mem _
  obtain ⟨z, rfl⟩ : x ∈ Set.range (comap p) := by
    rwa [range_comap_of_surjective _ _ hp, mem_zeroLocus]
  refine ⟨z, rfl, comap_injective_of_surjective _ (p.surjective_pullbackSnd_of_surjective q hp) ?_⟩
  simpa only [← comap_comp_apply, ← p.pullback_comm_sq q] using h

private theorem factorsThrough_comap_pullback (hp : Surjective p)
    {T : Type*} (l : PrimeSpectrum B → T) (r : PrimeSpectrum D → T)
    (h : ∀ z, l (comap p z) = r (comap q z)) :
    (Sum.elim l r).FactorsThrough
      (Sum.elim (comap (p.pullbackFst q)) (comap (p.pullbackSnd q))) := by
  have hr := comap_injective_of_surjective _ (p.surjective_pullbackSnd_of_surjective q hp)
  have hcross {x : PrimeSpectrum B} {y : PrimeSpectrum D}
      (hxy : comap (p.pullbackFst q) x = comap (p.pullbackSnd q) y) : l x = r y := by
    obtain ⟨z, rfl, rfl⟩ := p.exists_comap_eq_of_comap_pullbackFst_eq_comap_pullbackSnd q hp hxy
    exact h z
  rintro (x | x) (y | y) hxy
  · by_cases hx : comap (p.pullbackFst q) x ∈ Set.range (comap (p.pullbackSnd q))
    · obtain ⟨z, hz⟩ := hx
      exact (hcross hz.symm).trans (hcross (hxy.symm.trans hz.symm)).symm
    · rw [range_comap_of_surjective _ _ (p.surjective_pullbackSnd_of_surjective q hp),
        mem_zeroLocus] at hx
      obtain ⟨t, ht, htx⟩ := Set.not_subset.mp hx
      obtain ⟨_, _, huniq⟩ := p.existsUnique_comap_pullbackFst_of_notMem q ht htx
      exact congrArg l ((huniq x rfl).trans (huniq y hxy.symm).symm)
  · exact hcross hxy
  · exact (hcross hxy.symm).symm
  · exact congrArg r (hr hxy)

private theorem isClosed_of_isClosed_preimages_comap_pullback (hp : Surjective p)
    {W : Set (PrimeSpectrum (p.pullback q))}
    (hB : IsClosed (comap (p.pullbackFst q) ⁻¹' W))
    (hD : IsClosed (comap (p.pullbackSnd q) ⁻¹' W)) : IsClosed W := by
  obtain ⟨I, hI⟩ := (isClosed_iff_zeroLocus_ideal _).mp hB
  obtain ⟨J, hJ⟩ := (isClosed_iff_zeroLocus_ideal _).mp hD
  have hEq : comap p ⁻¹' zeroLocus I = comap q ⁻¹' zeroLocus J := by
    rw [← hI, ← hJ, ← Set.preimage_comp, ← Set.preimage_comp,
      ← comap_comp, ← comap_comp, p.pullback_comm_sq q]
  have hRad : (I.map p).radical = (J.map q).radical := by
    apply zeroLocus_eq_iff.mp
    simpa only [Ideal.map, zeroLocus_span, preimage_comap_zeroLocus] using hEq
  let K := I.comap (p.pullbackFst q) ⊓ J.comap (p.pullbackSnd q)
  refine (isClosed_iff_zeroLocus_ideal _).mpr ⟨K, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y | y, rfl⟩ := p.surjective_sumElim_comap_pullback q hp x
    · exact (mem_zeroLocus _ _).mpr <|
        inf_le_left.trans (Ideal.comap_mono ((mem_zeroLocus _ _).mp (hI ▸ hx)))
    · exact (mem_zeroLocus _ _).mpr <|
        inf_le_right.trans (Ideal.comap_mono ((mem_zeroLocus _ _).mp (hJ ▸ hx)))
  · intro x hx
    by_contra hxW
    have hxK : K ≤ x.asIdeal := (mem_zeroLocus _ _).mp hx
    by_cases hker : RingHom.ker (p.pullbackSnd q) ≤ x.asIdeal
    · -- On the closed locus a power of a separating element lifts across the surjection.
      obtain ⟨y, rfl⟩ : x ∈ Set.range (comap (p.pullbackSnd q)) := by
        rwa [range_comap_of_surjective _ _ (p.surjective_pullbackSnd_of_surjective q hp),
          mem_zeroLocus]
      have hy : ¬ J ≤ y.asIdeal := fun h ↦ hxW <|
        show y ∈ comap (p.pullbackSnd q) ⁻¹' W from hJ.symm ▸ (mem_zeroLocus _ _).mpr h
      obtain ⟨d, hd, hdy⟩ := Set.not_subset.mp hy
      have hdrad : q d ∈ (I.map p).radical :=
        hRad ▸ (Ideal.le_radical (Ideal.mem_map_of_mem q hd) : q d ∈ (J.map q).radical)
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hdrad
      have hn' : q d ^ (n + 1) ∈ I.map p := by
        rw [pow_succ']
        exact (I.map p).mul_mem_left _ hn
      obtain ⟨b, hb, hb_eq⟩ := (Ideal.mem_map_iff_of_surjective p hp).mp hn'
      let a : p.pullback q := ⟨(b, d ^ (n + 1)), hb_eq.trans (map_pow q d _).symm⟩
      have ha : a ∈ K := ⟨hb, J.pow_mem_of_mem hd _ (Nat.zero_lt_succ n)⟩
      exact hdy (y.isPrime.mem_of_pow_mem _ (hxK ha))
    · -- On the complement multiply by a kernel element to obtain a compatible pair.
      obtain ⟨t, ht, htx⟩ := Set.not_subset.mp hker
      obtain ⟨y, rfl, -⟩ := p.existsUnique_comap_pullbackFst_of_notMem q ht htx
      have hy : ¬ I ≤ y.asIdeal := fun h ↦ hxW <|
        show y ∈ comap (p.pullbackFst q) ⁻¹' W from hI.symm ▸ (mem_zeroLocus _ _).mpr h
      obtain ⟨b, hb, hby⟩ := Set.not_subset.mp hy
      have hp₀ : p (p.pullbackFst q t) = 0 := calc
        p (p.pullbackFst q t) = q (p.pullbackSnd q t) := t.property
        _ = 0 := by rw [RingHom.mem_ker.mp ht, map_zero]
      let a : p.pullback q := ⟨(p.pullbackFst q t * b, 0),
        show p (p.pullbackFst q t * b) = q 0 by rw [map_mul, hp₀, zero_mul, map_zero]⟩
      have ha : a ∈ K := ⟨I.mul_mem_left _ hb, J.zero_mem⟩
      exact hby ((y.isPrime.mem_or_mem (hxK ha)).resolve_left htx)

private theorem isQuotientMap_sumElim_comap_pullback (hp : Surjective p) :
    IsQuotientMap (Sum.elim (comap (p.pullbackFst q)) (comap (p.pullbackSnd q))) := by
  refine isQuotientMap_iff_isClosed.mpr ⟨p.surjective_sumElim_comap_pullback q hp, fun W ↦ ⟨?_, ?_⟩⟩
  · intro hW
    apply hW.preimage
    rw [continuous_sum_dom]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · intro hW
    exact p.isClosed_of_isClosed_preimages_comap_pullback q hp
      (hW.preimage continuous_inl) (hW.preimage continuous_inr)

/-- Along a surjection, taking spectra of a ring fiber product gives a pushout in `TopCat`. -/
theorem isPushout_base_spec_pullback (hp : Surjective p) :
    IsPushout (Spec.map (CommRingCat.ofHom p)).base (Spec.map (CommRingCat.ofHom q)).base
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base := by
  refine ⟨Scheme.forgetToTop.map_commSq (p.isPullback_spec_pullback q hp).toCommSq,
    ⟨PushoutCocone.isColimitAux' _ fun s ↦ ?_⟩⟩
  let π := Sum.elim (comap (p.pullbackFst q)) (comap (p.pullbackSnd q))
  have hπ := p.isQuotientMap_sumElim_comap_pullback q hp
  have hfactor := p.factorsThrough_comap_pullback q hp s.inl s.inr
    (ConcreteCategory.congr_hom s.condition)
  let lift : PrimeSpectrum (p.pullback q) → s.pt := Sum.elim s.inl s.inr ∘ surjInv hπ.surjective
  have hlift : lift ∘ π = Sum.elim s.inl s.inr :=
    funext fun z ↦ hfactor (rightInverse_surjInv hπ.surjective (π z))
  have hc : Continuous lift := hπ.continuous_iff.mpr
    (hlift.symm ▸ continuous_sum_dom.mpr ⟨s.inl.hom.continuous, s.inr.hom.continuous⟩)
  refine ⟨TopCat.ofHom ⟨lift, hc⟩, ?_, ?_, ?_⟩
  · ext z
    exact congrFun hlift (Sum.inl z)
  · ext z
    exact congrFun hlift (Sum.inr z)
  · intro m hl hr
    ext z
    obtain ⟨x | x, rfl⟩ := hπ.surjective z
    · exact (ConcreteCategory.congr_hom hl x).trans (congrFun hlift (Sum.inl x)).symm
    · exact (ConcreteCategory.congr_hom hr x).trans (congrFun hlift (Sum.inr x)).symm

end RingHom
