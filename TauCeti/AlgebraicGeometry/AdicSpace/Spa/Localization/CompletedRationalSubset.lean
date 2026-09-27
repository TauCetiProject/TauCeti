/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedHomeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.RationalSubset
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.DenseRange

/-!
# Rational subsets of the completed rational localization

For a rational subset `R(T/s)` of `Spa (A, A⁺)`, `spaCompletedLocalizationHomeomorph` identifies
`Spa (A⟨T/s⟩, A_U⁺)` with `R(T/s)`. This file shows that the identification matches rational
subsets: pullback along the structure map `ρ : A → A⟨T/s⟩` is a bijection between the rational
subsets of `Spa (A, A⁺)` contained in `R(T/s)` and the rational subsets of `Spa (A⟨T/s⟩, A_U⁺)`.
That is the second assertion of Wedhorn, *Adic Spaces*, Proposition 8.2 (2); the first assertion
is the homeomorphism itself.

The argument factors the *ring* homomorphism rather than the homeomorphism. The structure map is
the composite `A → Aₛ → A⟨T/s⟩` of the localization map with the completion map, so `spaComapLoc`
is the composite of the two corresponding `spaComap`s — this is
`TauCeti.ValuationSpectrum.spaComapLoc_eq_comp` in `Spa/Localization/Basic.lean`, and it is what
the two descent results below rewrite with. Each factor carries rational subsets in both
directions: the localization factor by clearing denominators, the completion factor because the
completion map has dense range. The structure map itself need not have dense range — `A` is in
general not dense in `Aₛ` — so the factorization is not a convenience but the route.

No completeness, Tate or Noetherian hypothesis is needed, and `A⁺` is an arbitrary subring
subject only to the hypothesis `A₀ ≤ A⁺` that the homeomorphism already carries.

## Main definitions

* `TauCeti.ValuationSpectrum.locOpensComap`: the pullback of an open of `Spa (A, A⁺)` along
  `spaComapLoc`, as an open of `Spa (A⟨T/s⟩, A_U⁺)`.

## Main results

* `TauCeti.ValuationSpectrum.locOpensComap_spaBasicOpen`: the pullback of the basic open
  `R(T'/s')` is `R(ρ(T')/ρ(s'))`.
* `TauCeti.ValuationSpectrum.spaComapLoc_preimage_mem_spaRationalFamily` and
  `TauCeti.ValuationSpectrum.exists_mem_spaRationalFamily_spaComapLoc_preimage_eq`: the rational
  subsets of `Spa (A⟨T/s⟩, A_U⁺)` are exactly the preimages under `ρ` of the rational subsets of
  `Spa (A, A⁺)`.
* `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph_preimage_mem_spaRationalFamily`,
  `exists_mem_spaRationalFamily_spaCompletedLocalizationHomeomorph_preimage_eq` and
  `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph_image_mem_spaRationalFamily`: the
  same two statements phrased through the homeomorphism, together with the image form.
* `TauCeti.ValuationSpectrum.bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily`:
  Wedhorn Proposition 8.2 (2), second assertion — the bijection between the rational subsets of
  `Spa (A, A⁺)` contained in `R(T/s)` and the rational subsets of `Spa (A⟨T/s⟩, A_U⁺)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2 (2), second
  assertion.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Rational subsets pull back to rational subsets along the structure map.** The preimage
under `ρ : A → A⟨T/s⟩` of a member of the rational family of `Spa (A, A⁺)` is a member of the
rational family of `Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem spaComapLoc_preimage_mem_spaRationalFamily (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {W : Set (spa Aplus)}
    (hW : W ∈ spaRationalFamily Aplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spaComapLoc P Aplus T s S hden ⁻¹' W ∈
      spaRationalFamily (completedPlusSubring P Aplus T s S hden) := by
  classical
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  -- the localization map is continuous at `locTopology`, which is the uniformity's topology only
  -- after transporting along `locUniformSpace_toTopologicalSpace`
  have hcont : Continuous (algebraMap A S) := by
    have h := continuous_algebraMap_locTopology P T s S hden
    rwa [← locUniformSpace_toTopologicalSpace P T s S hden] at h
  obtain ⟨V, r, hV, rfl⟩ := mem_spaRationalFamily_iff.mp hW
  -- the set identity is the two-step form of `spaComap_preimage_rationalSubset`; what is left is
  -- that the numerator ideal stays open, which holds for each factor separately
  rw [spaComapLoc_eq_comp P Aplus T s S hden hcont
      (algebraMap_mem_integralClosure_adjoin_plus Aplus T s S) Completion.continuous_coeRingHom
      fun _ hx ↦ coeRingHom_mem_completedPlusSubring P Aplus T s S hden hx,
    Set.preimage_comp, spaComap_preimage_rationalSubset, spaComap_preimage_rationalSubset]
  refine mem_spaRationalFamily_iff.mpr ⟨_, _, ?_, rfl⟩
  -- the numerator ideal is carried to an open ideal by each of the two factors in turn
  rw [Finset.coe_image, ← Ideal.map_span]
  refine isOpen_map_coeRingHom ?_
  rw [Finset.coe_image, ← Ideal.map_span]
  have hopen := isOpen_map_algebraMap_locTopology P T s S hden hV
  rwa [← locUniformSpace_toTopologicalSpace P T s S hden] at hopen

/-- **Every rational subset of `Spa (A⟨T/s⟩, A_U⁺)` is pulled back from one of `Spa (A, A⁺)`.**
This is the substantial direction of Wedhorn Proposition 8.2 (2).

The rational subset obtained downstairs need not be contained in `R(T/s)`; only its trace on
`R(T/s)` is determined. -/
theorem exists_mem_spaRationalFamily_spaComapLoc_preimage_eq (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ U ∈ spaRationalFamily (completedPlusSubring P Aplus T s S hden),
      ∃ W ∈ spaRationalFamily Aplus, spaComapLoc P Aplus T s S hden ⁻¹' W = U := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  have hcont : Continuous (algebraMap A S) := by
    have h := continuous_algebraMap_locTopology P T s S hden
    rwa [← locUniformSpace_toTopologicalSpace P T s S hden] at h
  intro U hU
  -- descend through the completion map, whose range is dense
  obtain ⟨V, hV, hVU⟩ := exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange
    Completion.continuous_coeRingHom Completion.denseRange_coe
    (integralClosure ↥(Algebra.adjoin Aplus
      (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring
    (completedPlusSubring P Aplus T s S hden)
    (fun _ hx ↦ coeRingHom_mem_completedPlusSubring P Aplus T s S hden hx) hU
  -- then through the localization map, by clearing denominators
  obtain ⟨W, hW, hWV⟩ := exists_mem_spaRationalFamily_spaComap_preimage_eq_of_isLocalization
    (Submonoid.powers s) Aplus _ hcont
    (algebraMap_mem_integralClosure_adjoin_plus Aplus T s S) hV
  refine ⟨W, hW, ?_⟩
  rw [spaComapLoc_eq_comp P Aplus T s S hden hcont
      (algebraMap_mem_integralClosure_adjoin_plus Aplus T s S) Completion.continuous_coeRingHom
      fun _ hx ↦ coeRingHom_mem_completedPlusSubring P Aplus T s S hden hx,
    Set.preimage_comp, hWV, hVU]

/-- **Rational subsets pull back to rational subsets through the homeomorphism.** The preimage
under `spaCompletedLocalizationHomeomorph` of the trace on `R(T/s)` of a member of the rational
family of `Spa (A, A⁺)` is a member of the rational family of `Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem spaCompletedLocalizationHomeomorph_preimage_mem_spaRationalFamily (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {W : Set (spa Aplus)} (hW : W ∈ spaRationalFamily Aplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spaCompletedLocalizationHomeomorph P Aplus hP T s S hden ⁻¹' (Subtype.val ⁻¹' W) ∈
      spaRationalFamily (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [← Set.preimage_comp, val_comp_spaCompletedLocalizationHomeomorph]
  exact spaComapLoc_preimage_mem_spaRationalFamily P Aplus T s S hden hW

/-- **Every rational subset of `Spa (A⟨T/s⟩, A_U⁺)` is pulled back through the homeomorphism.**
The homeomorphism-phrased form of `exists_mem_spaRationalFamily_spaComapLoc_preimage_eq`. -/
theorem exists_mem_spaRationalFamily_spaCompletedLocalizationHomeomorph_preimage_eq
    (P : PairOfDefinition A) (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ U ∈ spaRationalFamily (completedPlusSubring P Aplus T s S hden),
      ∃ W ∈ spaRationalFamily Aplus,
        spaCompletedLocalizationHomeomorph P Aplus hP T s S hden ⁻¹' (Subtype.val ⁻¹' W) = U := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro U hU
  obtain ⟨W, hW, hWU⟩ :=
    exists_mem_spaRationalFamily_spaComapLoc_preimage_eq P Aplus T s S hden U hU
  refine ⟨W, hW, ?_⟩
  rw [← Set.preimage_comp, val_comp_spaCompletedLocalizationHomeomorph]
  exact hWU

/-- **Rational subsets push forward to rational subsets through the homeomorphism.** The image in
`Spa (A, A⁺)` of a member of the rational family of `Spa (A⟨T/s⟩, A_U⁺)` is a member of the
rational family of `Spa (A, A⁺)`.

The image is automatically contained in `R(T/s)`, and it is the openness of the numerator ideal
of `R(T/s)` that keeps the intersection with `R(T/s)` inside the rational family. -/
theorem spaCompletedLocalizationHomeomorph_image_mem_spaRationalFamily (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ U ∈ spaRationalFamily (completedPlusSubring P Aplus T s S hden),
      Subtype.val '' (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden '' U) ∈
        spaRationalFamily Aplus := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro U hU
  obtain ⟨W, hW, rfl⟩ :=
    exists_mem_spaRationalFamily_spaCompletedLocalizationHomeomorph_preimage_eq
      P Aplus hP T s S hden U hU
  -- the homeomorphism is surjective, so the image of the preimage is the trace on `R(T/s)`,
  -- whose image in `Spa (A, A⁺)` is the intersection with `R(T/s)`
  rw [Set.image_preimage_eq _
      (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).surjective,
    Subtype.image_preimage_coe]
  exact inter_mem_spaRationalFamily_of_pairOfDefinition P
    (mem_spaRationalFamily_iff.mpr ⟨T, s, hT, rfl⟩) hW

/-- **Wedhorn, *Adic Spaces*, Proposition 8.2 (2), second assertion.** Pullback along the
structure map `ρ : A → A⟨T/s⟩` is a bijection between the rational subsets of `Spa (A, A⁺)`
contained in `R(T/s)` and the rational subsets of `Spa (A⟨T/s⟩, A_U⁺)`.

The statement is a `Set.BijOn` rather than an `Iff` between memberships because the codomain of
the homeomorphism is the *subtype* `↥R(T/s)`: pullback is not injective on all subsets of
`Spa (A, A⁺)`, since two rational subsets with the same trace on `R(T/s)` have the same preimage.
Restricting the domain to the rational subsets contained in `R(T/s)` is what makes it injective,
and every rational subset of `Spa (A⟨T/s⟩, A_U⁺)` is still hit, because a rational subset may be
intersected with `R(T/s)` without changing its preimage. -/
theorem bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Set.BijOn (fun W : Set (spa Aplus) ↦
        spaCompletedLocalizationHomeomorph P Aplus hP T s S hden ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily Aplus | W ⊆ Subtype.val ⁻¹' rationalSubset Aplus T s}
      (spaRationalFamily (completedPlusSubring P Aplus T s S hden)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have hR : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) ∈
      spaRationalFamily Aplus := mem_spaRationalFamily_iff.mpr ⟨T, s, hT, rfl⟩
  -- taking the image back is a left inverse on subsets contained in `R(T/s)`, which is where the
  -- containment hypothesis is used; it is unused for `Set.MapsTo`
  have hleft : Set.LeftInvOn
      (fun U ↦ Subtype.val '' (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden '' U))
      (fun W : Set (spa Aplus) ↦
        spaCompletedLocalizationHomeomorph P Aplus hP T s S hden ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily Aplus | W ⊆ Subtype.val ⁻¹' rationalSubset Aplus T s} := by
    intro W hW
    simp only [Set.image_preimage_eq _
        (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).surjective,
      Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right hW.2]
  refine ⟨fun W hW ↦ spaCompletedLocalizationHomeomorph_preimage_mem_spaRationalFamily P Aplus hP
    T s S hden hW.1, hleft.injOn, fun U hU ↦ ?_⟩
  obtain ⟨W, hW, hWU⟩ :=
    exists_mem_spaRationalFamily_spaCompletedLocalizationHomeomorph_preimage_eq
      P Aplus hP T s S hden U hU
  -- intersecting with `R(T/s)` does not change the preimage, because `R(T/s)` pulls back to
  -- everything, and it lands the subset inside `R(T/s)` as the domain requires
  refine ⟨W ∩ Subtype.val ⁻¹' rationalSubset Aplus T s,
    ⟨inter_mem_spaRationalFamily_of_pairOfDefinition P hW hR, Set.inter_subset_right⟩, ?_⟩
  simp only [Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ]
  exact hWU

/-! ### Pulling back opens along the structure map -/

section locOpensComap

open _root_.TopologicalSpace

variable (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

/-- **The pullback of an open along `Spa` of the structure map**: for an open `V` of `Spa (A, A⁺)`,
the open `j⁻¹(V)` of `Spa (A⟨T/s⟩, A_U⁺)`, where `j = spaComapLoc` is induced by the structure map
`A → A⟨T/s⟩`. Membership is `mem_locOpensComap`. -/
noncomputable def locOpensComap (V : Opens ↥(spa Aplus)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Opens ↥(spa (completedPlusSubring P Aplus T s S hden)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  Opens.comap ⟨spaComapLoc P Aplus T s S hden, continuous_spaComapLoc P Aplus T s S hden⟩ V

/-- A point of `Spa (A⟨T/s⟩, A_U⁺)` lies in `locOpensComap … V` exactly when its image under
`spaComapLoc` lies in `V`. -/
@[simp]
theorem mem_locOpensComap (V : Opens ↥(spa Aplus)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      v ∈ locOpensComap P Aplus T s S hden V ↔ spaComapLoc P Aplus T s S hden v ∈ V :=
  fun _ ↦ Iff.rfl

/-- Pulling back along `spaComapLoc` preserves containment of opens. -/
theorem locOpensComap_mono {V V' : Opens ↥(spa Aplus)} (h : V' ≤ V) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    locOpensComap P Aplus T s S hden V' ≤ locOpensComap P Aplus T s S hden V :=
  fun _ hv ↦ h hv

open scoped Classical in
/-- **The pullback of a basic open**: pulling `R(T'/s')` back along `spaComapLoc` gives the basic
open `R(ρ(T')/ρ(s'))` of `Spa (A⟨T/s⟩, A_U⁺)`, where `ρ : A → A⟨T/s⟩` is the structure map. -/
@[simp]
theorem locOpensComap_spaBasicOpen (T' : Finset A) (s' : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    locOpensComap P Aplus T s S hden (spaBasicOpen Aplus T' s') =
      spaBasicOpen (completedPlusSubring P Aplus T s S hden)
        (T'.image (toCompletionLoc P T s S hden)) (toCompletionLoc P T s S hden s') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  ext v
  simp only [SetLike.mem_coe, mem_locOpensComap, mem_spaBasicOpen, spaComapLoc_val]
  rw [← comap_preimage_rationalSubset_inter_spa (toCompletionLoc P T s S hden)
    (continuous_toCompletionLoc P T s S hden)
    fun _ ha ↦ toCompletionLoc_mem_completedPlusSubring P Aplus T s S hden ha]
  exact ⟨fun h ↦ ⟨h, v.2⟩, And.left⟩

end locOpensComap

end TauCeti.ValuationSpectrum

end
