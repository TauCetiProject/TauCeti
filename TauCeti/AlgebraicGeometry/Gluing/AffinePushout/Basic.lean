/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.LocalRing.Pullback

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.RingTheory.FiberProduct.Basic
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.Topology.Category.TopCat.Pushout

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

/-- The map `Spec B → Spec (B ×_C D)` is finite when `p` is surjective and `q` is finite. -/
theorem isFinite_spec_pullbackFst (hp : Surjective p) (hq : q.Finite) :
    IsFinite (Spec.map (CommRingCat.ofHom (p.pullbackFst q))) :=
  (IsFinite.SpecMap_iff _).mpr (p.finite_pullbackFst_of_surjective q hp hq)

/-- The first projection induces an isomorphism over the basic open of an element in the kernel
of the second projection. -/
theorem isIso_spec_pullbackFst_restrict_basicOpen_of_mem_ker_pullbackSnd
    {t : p.pullback q}
    (ht : t ∈ RingHom.ker (p.pullbackSnd q)) :
    IsIso (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ∣_ PrimeSpectrum.basicOpen t) :=
  (isIso_SpecMap_morphismRestrict_basicOpen_iff
    (CommRingCat.ofHom (p.pullbackFst q)) t).mpr
    (p.bijective_away_map_pullbackFst_of_mem_ker_pullbackSnd q (Localization.Away t)
      (Localization.Away (p.pullbackFst q t)) ht)

/-- The map from `Spec B` is an isomorphism over the complement of
`V(ker (p.pullbackSnd q))`, with domain the inverse image of that complement.
When `p` is surjective, this zero locus is the image of `Spec D`. -/
theorem isIso_spec_pullbackFst_restrict_compl_zeroLocus_ker_pullbackSnd :
    IsIso (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ∣_
      (⟨(zeroLocus (RingHom.ker (p.pullbackSnd q))).compl,
        (isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (CommRingCat.of (p.pullback q))).Opens)) := by
  let f := Spec.map (CommRingCat.ofHom (p.pullbackFst q))
  let U : RingHom.ker (p.pullbackSnd q) → (Spec (CommRingCat.of (p.pullback q))).Opens :=
    fun t ↦ PrimeSpectrum.basicOpen t.val
  have hU : (⨆ t, U t) =
      (⟨(zeroLocus (RingHom.ker (p.pullbackSnd q))).compl,
        (isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (CommRingCat.of (p.pullback q))).Opens) := by
    exact iSup_basicOpen_eq_compl_zeroLocus _
  have h : IsIso (f ∣_ iSup U) :=
    f.isIso_morphismRestrict_iSup U fun t ↦
      p.isIso_spec_pullbackFst_restrict_basicOpen_of_mem_ker_pullbackSnd q t.property
  exact hU ▸ h

private theorem existsUnique_comap_pullbackFst_of_notMem {t : p.pullback q}
    (ht : t ∈ RingHom.ker (p.pullbackSnd q)) {x : PrimeSpectrum (p.pullback q)}
    (hx : t ∉ x.asIdeal) :
    ∃! y : PrimeSpectrum B, comap (p.pullbackFst q) y = x := by
  let f := Spec.map (CommRingCat.ofHom (p.pullbackFst q))
  let U : (Spec (CommRingCat.of (p.pullback q))).Opens := PrimeSpectrum.basicOpen t
  have hxU : x ∈ U := (mem_basicOpen t x).mpr hx
  have : IsIso (f ∣_ U) :=
    p.isIso_spec_pullbackFst_restrict_basicOpen_of_mem_ker_pullbackSnd q ht
  have hf : (f : PrimeSpectrum B → PrimeSpectrum (p.pullback q)) = comap (p.pullbackFst q) :=
    funext (Spec.map_apply (CommRingCat.ofHom (p.pullbackFst q)))
  rw [← hf]
  exact f.existsUnique_apply_eq_of_isIso_morphismRestrict U hxU

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

private theorem le_asIdeal_of_comap_pullbackSnd (hp : Surjective p) {I : Ideal B} {J : Ideal D}
    (hRad : (I.map p).radical = (J.map q).radical) (y : PrimeSpectrum D)
    (hy : I.comap (p.pullbackFst q) ⊓ J.comap (p.pullbackSnd q) ≤
      (comap (p.pullbackSnd q) y).asIdeal) :
    J ≤ y.asIdeal := by
  intro d hd
  have hdrad : q d ∈ (I.map p).radical :=
    hRad ▸ (Ideal.le_radical (Ideal.mem_map_of_mem q hd) : q d ∈ (J.map q).radical)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hdrad
  have hn' : q d ^ (n + 1) ∈ I.map p := by
    rw [pow_succ']
    exact (I.map p).mul_mem_left _ hn
  obtain ⟨b, hb, hb_eq⟩ := (Ideal.mem_map_iff_of_surjective p hp).mp hn'
  let a : p.pullback q := ⟨(b, d ^ (n + 1)), hb_eq.trans (map_pow q d _).symm⟩
  have ha : a ∈ I.comap (p.pullbackFst q) ⊓ J.comap (p.pullbackSnd q) :=
    ⟨hb, J.pow_mem_of_mem hd _ (Nat.zero_lt_succ n)⟩
  exact y.isPrime.mem_of_pow_mem _ (hy ha)

private theorem le_asIdeal_of_comap_pullbackFst {I : Ideal B} {J : Ideal D}
    (y : PrimeSpectrum B) {t : p.pullback q} (ht : t ∈ RingHom.ker (p.pullbackSnd q))
    (hty : t ∉ (comap (p.pullbackFst q) y).asIdeal)
    (hy : I.comap (p.pullbackFst q) ⊓ J.comap (p.pullbackSnd q) ≤
      (comap (p.pullbackFst q) y).asIdeal) :
    I ≤ y.asIdeal := by
  intro b hb
  let t₀ : RingHom.ker (p.pullbackSnd q) := ⟨t, ht⟩
  have ht₀ : (p.pullbackSndKerEquiv q t₀ : B) ∈ RingHom.ker p :=
    (p.pullbackSndKerEquiv q t₀).property
  let b₀ : RingHom.ker p := ⟨p.pullbackFst q t * b, by
    apply (RingHom.ker p).mul_mem_right
    simpa only [pullbackSndKerEquiv_apply_coe] using ht₀⟩
  let a : p.pullback q := (p.pullbackSndKerEquiv q).symm b₀
  have hI : a ∈ I.comap (p.pullbackFst q) := Ideal.mem_comap.mpr (by
    rw [pullbackSndKerEquiv_symm_fst]
    exact I.mul_mem_left _ hb)
  have hJ : a ∈ J.comap (p.pullbackSnd q) := Ideal.mem_comap.mpr (by
    rw [pullbackSndKerEquiv_symm_snd]
    exact J.zero_mem)
  have hab : p.pullbackFst q a ∈ y.asIdeal := Ideal.mem_comap.mp (hy ⟨hI, hJ⟩)
  rw [pullbackSndKerEquiv_symm_fst] at hab
  exact (y.isPrime.mem_or_mem hab).resolve_left hty

private theorem isClosed_of_isClosed_preimages_comap_pullback (hp : Surjective p)
    {W : Set (PrimeSpectrum (p.pullback q))}
    (hB : IsClosed (comap (p.pullbackFst q) ⁻¹' W))
    (hD : IsClosed (comap (p.pullbackSnd q) ⁻¹' W)) : IsClosed W := by
  obtain ⟨I, hI⟩ := (isClosed_iff_zeroLocus_ideal _).mp hB
  obtain ⟨J, hJ⟩ := (isClosed_iff_zeroLocus_ideal _).mp hD
  have hComp : comap (p.pullbackFst q) ∘ comap p = comap (p.pullbackSnd q) ∘ comap q := by
    rw [← comap_comp, ← comap_comp, p.pullback_comm_sq q]
  have hEq : zeroLocus (I.map p : Set C) = zeroLocus (J.map q : Set C) := by
    have hpre := congrArg (fun f : PrimeSpectrum C → PrimeSpectrum (p.pullback q) ↦ f ⁻¹' W)
      hComp
    simp only [Set.preimage_comp, hI, hJ, preimage_comap_zeroLocus] at hpre
    rwa [← zeroLocus_span (p '' (I : Set B)), ← Ideal.map,
      ← zeroLocus_span (q '' (J : Set D)), ← Ideal.map] at hpre
  have hRad := zeroLocus_eq_iff.mp hEq
  let K := I.comap (p.pullbackFst q) ⊓ J.comap (p.pullbackSnd q)
  refine (isClosed_iff_zeroLocus_ideal _).mpr ⟨K, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y | y, rfl⟩ := p.surjective_sumElim_comap_pullback q hp x
    · have hy : y ∈ zeroLocus (I : Set B) := hI ▸ Set.mem_preimage.mpr hx
      exact (mem_zeroLocus _ _).mpr <|
        inf_le_left.trans (Ideal.comap_mono ((mem_zeroLocus _ _).mp hy))
    · have hy : y ∈ zeroLocus (J : Set D) := hJ ▸ Set.mem_preimage.mpr hx
      exact (mem_zeroLocus _ _).mpr <|
        inf_le_right.trans (Ideal.comap_mono ((mem_zeroLocus _ _).mp hy))
  · intro x hx
    have hxK : K ≤ x.asIdeal := (mem_zeroLocus _ _).mp hx
    by_cases hker : RingHom.ker (p.pullbackSnd q) ≤ x.asIdeal
    · obtain ⟨y, rfl⟩ : x ∈ Set.range (comap (p.pullbackSnd q)) := by
        rwa [range_comap_of_surjective _ _ (p.surjective_pullbackSnd_of_surjective q hp),
          mem_zeroLocus]
      exact Set.mem_preimage.mp (hJ.symm ▸ (mem_zeroLocus y _).mpr
        (p.le_asIdeal_of_comap_pullbackSnd q hp hRad y hxK))
    · obtain ⟨t, ht, htx⟩ := Set.not_subset.mp hker
      obtain ⟨y, rfl, -⟩ := p.existsUnique_comap_pullbackFst_of_notMem q ht htx
      exact Set.mem_preimage.mp (hI.symm ▸ (mem_zeroLocus y _).mpr
        (p.le_asIdeal_of_comap_pullbackFst q y ht htx hxK))

private theorem eq_of_notMem_range_of_comap_pullbackFst_eq (hp : Surjective p)
    (x y : PrimeSpectrum B) (hx : x ∉ Set.range (comap p))
    (hxy : comap (p.pullbackFst q) x = comap (p.pullbackFst q) y) : x = y := by
  rw [range_comap_of_surjective _ _ hp, mem_zeroLocus] at hx
  have hx' : ¬ RingHom.ker (p.pullbackSnd q) ≤ (comap (p.pullbackFst q) x).asIdeal := by
    rwa [comap_asIdeal, ← Ideal.map_le_iff_le_comap, p.map_pullbackFst_ker_pullbackSnd_eq q]
  obtain ⟨t, ht, htx⟩ := Set.not_subset.mp hx'
  obtain ⟨_, _, huniq⟩ := p.existsUnique_comap_pullbackFst_of_notMem q ht htx
  exact (huniq x rfl).trans (huniq y hxy.symm).symm

/-- Along a surjection, taking spectra of a ring fiber product gives a pushout in `TopCat`.
A subset is open in this pushout exactly when its inverse images in `Spec B` and `Spec D`
are open. -/
theorem isPushout_base_spec_pullback (hp : Surjective p) :
    IsPushout (Spec.map (CommRingCat.ofHom p)).base (Spec.map (CommRingCat.ofHom q)).base
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base := by
  let F := Scheme.forgetToTop ⋙ forget TopCat
  have hs := (p.isPullback_spec_pullback q hp).flip
  have hpre := hs.toCommSq.map F
  let fst := F.map (Spec.map (CommRingCat.ofHom (p.pullbackFst q)))
  let snd := F.map (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)))
  have hfst : (fst : PrimeSpectrum B → PrimeSpectrum (p.pullback q)) = comap (p.pullbackFst q) :=
    funext (Spec.map_apply (CommRingCat.ofHom (p.pullbackFst q)))
  have hsnd : (snd : PrimeSpectrum D → PrimeSpectrum (p.pullback q)) = comap (p.pullbackSnd q) :=
    funext (Spec.map_apply (CommRingCat.ofHom (p.pullbackSnd q)))
  have hpmap : (Spec.map (CommRingCat.ofHom p) : PrimeSpectrum C → PrimeSpectrum B) = comap p :=
    funext (Spec.map_apply (CommRingCat.ofHom p))
  have hinj : Injective snd := by
    rw [hsnd]
    exact comap_injective_of_surjective _ (p.surjective_pullbackSnd_of_surjective q hp)
  have : Mono snd := (mono_iff_injective _).mpr hinj
  have hSet : IsPullback (F.map (Spec.map (CommRingCat.ofHom q)))
      (F.map (Spec.map (CommRingCat.ofHom p))) snd fst := by
    refine (Types.isPullback_iff ..).mpr ⟨hpre.w, ?_, ?_⟩
    · intro x y h
      have he : Spec.map (CommRingCat.ofHom p) x = Spec.map (CommRingCat.ofHom p) y := h.2
      rw [hpmap] at he
      exact comap_injective_of_surjective _ hp he
    · exact Scheme.exists_preimage_of_isPullback hs
  -- Apply Tau Ceti's `IsPushout.of_isPushout_forget` to the underlying set pushout
  -- given by Mathlib's `Types.isPushout_of_isPullback_of_mono'`.
  apply IsPushout.of_isPushout_forget
  · refine (Types.isPushout_of_isPullback_of_mono' hSet ?_ ?_).flip
    · rw [hfst, hsnd]
      refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨y | y, hy⟩ := p.surjective_sumElim_comap_pullback q hp x
      · exact Or.inr ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
    · intro x y hx _ hxy
      have hx' : x ∉ Set.range (Spec.map (CommRingCat.ofHom p)) := hx
      rw [hpmap] at hx'
      rw [hfst] at hxy
      exact p.eq_of_notMem_range_of_comap_pullbackFst_eq q hp x y hx' hxy
  · intro W hB hD
    -- Use the prime-spectrum presentation to apply the closed-set criterion.
    let W' : Set (PrimeSpectrum (p.pullback q)) := W
    have hB' : @IsOpen (PrimeSpectrum B) _ (fst ⁻¹' W') := hB
    have hD' : @IsOpen (PrimeSpectrum D) _ (snd ⁻¹' W') := hD
    rw [hfst] at hB'
    rw [hsnd] at hD'
    have h : IsClosed W'ᶜ := p.isClosed_of_isClosed_preimages_comap_pullback q hp
      (by rw [Set.preimage_compl]; exact hB'.isClosed_compl)
      (by rw [Set.preimage_compl]; exact hD'.isClosed_compl)
    exact (by simpa only [compl_compl] using h.isOpen_compl : IsOpen W')

end RingHom
