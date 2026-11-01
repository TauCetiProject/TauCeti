/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.TensorProduct.Map

/-!
# Completed tensor products of completed localisations

Let `A → B` and `A → C` be adic homomorphisms of Huber rings and `D = B ⊗̂_A C` their separated
completed tensor ring, with coprojections `inl : B → D` and `inr : C → D`. Localising the factors
at `s ∈ B` with numerators `T` and at `s' ∈ C` with numerators `T'` and then taking the completed
tensor product gives the localisation of `D` at the common denominator `inl(s) · inr(s')`:

```text
B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩ ≅ D⟨T''/(inl(s) · inr(s'))⟩,
T'' = ({inl(s)} ∪ inl(T)) · ({inr(s')} ∪ inr(T')).
```

These are the numerators of the intersection of two rational subsets
(`TauCeti.ValuationSpectrum.rationalSubset_inter`): on adic spectra the right-hand side
corresponds to the intersection of the preimages of `R(T/s)` and `R(T'/s')` under the two
coprojections, whose preimages are `R(inl(T)/inl(s))` and `R(inr(T')/inr(s'))`
(`TauCeti.Huber.Pair.Hom.spaComap_preimage_rationalSubset`). So this is the ring-level statement
that completed rational localisation commutes with completed tensor products, as needed to compare
the rational subsets of a fibre product of affinoid adic spaces with those of its factors.

Both directions of the isomorphism come from universal properties. A map out of `B⟨T/s⟩` is
determined by a continuous map out of `B` inverting `s` and making the fractions `t/s`
power-bounded
(`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`),
and a map out of the completed tensor ring by compatible continuous maps out of the factors
(`TauCeti.Huber.CompletedTensor.lift`). The two composites are the identity because continuous maps
out of either side are determined by their restrictions to `B` and `C`. Only the topological rings
are compared; rings of integral elements are not.

## Main definitions

* `TauCeti.Huber.CompletedTensor.completionLocEquiv`: the ring isomorphism
  `B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩ ≃+* D⟨T''/(inl(s) · inr(s'))⟩`.

## Main results

* `TauCeti.Huber.CompletedTensor.hasDenominatorPower_inl_mul_inr`: if `T · B` and `T' · C` are
  open, the localisation of `D` at `T''` and `inl(s) · inr(s')` is defined.
* `TauCeti.Huber.CompletedTensor.isHomeomorph_completionLocEquiv`: the isomorphism is a
  homeomorphism.
* `TauCeti.Huber.CompletedTensor.completionLocEquiv_inl_toCompletionLoc` and `…_inr_…`: it sends
  `b ⊗ 1` and `1 ⊗ c` to the images of `inl(b)` and `inr(c)`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51.
-/

public section

open UniformSpace

namespace TauCeti.Huber.CompletedTensor

open PairOfDefinition

open scoped Pointwise

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
  [Algebra A C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]

/-- If `T · B` and `T' · C` are open, the standing hypothesis of the localisation of `B ⊗̂_A C` at
the numerators `insert (inl s) (inl T) * insert (inr s') (inr T')` and the denominator
`inl(s) · inr(s')` holds, for every pair of definition. These are the numerators presenting the
intersection of the preimages of `R(T/s)` and `R(T'/s')`
(`TauCeti.ValuationSpectrum.rationalSubset_inter`). -/
theorem hasDenominatorPower_inl_mul_inr (Q : PairOfDefinition (CompletedTensor A B C))
    {T : Finset B} {s : B} {T' : Finset C} {s' : C}
    (hT : IsOpen (Ideal.span (T : Set B) : Set B)) (hT' : IsOpen (Ideal.span (T' : Set C) : Set C))
    (S'' : Type*) [CommRing S''] [Algebra (CompletedTensor A B C) S'']
    [IsLocalization.Away (inl A B C s * inr A B C s') S''] :
    HasDenominatorPower Q
      (insert (inl A B C s) (T.image (inl A B C)) *
        insert (inr A B C s') (T'.image (inr A B C)) : Finset _)
      (inl A B C s * inr A B C s') S'' := by
  refine hasDenominatorPower_mul Q (inl A B C '' T) (inr A B C '' T') _ _ _
    (Localization.Away (inl A B C s))
    (Localization.Away (inr A B C s')) S'' ?_ ?_
    (hasDenominatorPower_of_isOpen_span Q _ _ _
      (by rw [← Ideal.map_span]; exact (isAdicHom_inl A B C).isOpen_map hT))
    (hasDenominatorPower_of_isOpen_span Q _ _ _
      (by rw [← Ideal.map_span]; exact (isAdicHom_inr A B C).isOpen_map hT'))
  · rintro _ ⟨t, ht, rfl⟩
    exact Finset.mul_mem_mul (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))
      (Finset.mem_insert_self _ _)
  · rintro _ ⟨t', ht', rfl⟩
    rw [Finset.mem_coe, mul_comm (inr A B C t')]
    exact Finset.mul_mem_mul (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht'))

variable (P : PairOfDefinition B) (T : Finset B) (s : B) (S : Type*) [CommRing S] [Algebra B S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (T' : Finset C) (s' : C) (S' : Type*) [CommRing S'] [Algebra C S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S''] [IsLocalization.Away (inl A B C s * inr A B C s') S'']
  (hden'' : HasDenominatorPower Q
    (insert (inl A B C s) (T.image (inl A B C)) *
      insert (inr A B C s') (T'.image (inr A B C)) : Finset _)
    (inl A B C s * inr A B C s') S'')

/-! ### The map `B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩ → D⟨T''/s''⟩` -/

/-- `B → D → D⟨T''/s''⟩` extends to `B⟨T/s⟩`: `inl(s)` divides the denominator, and `t/s` is the
fraction `(inl(t) · inr(s'))/(inl(s) · inr(s'))`. -/
private theorem existsUnique_leftLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∃! g : Completion S →+* Completion S'', Continuous g ∧
      g.comp (toCompletionLoc P T s S hden) =
        (toCompletionLoc Q _ _ S'' hden'').comp (inl A B C) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  have hu := isUnit_toCompletionLoc_of_dvd Q _ _ S'' hden''
    (dvd_mul_right (inl A B C s) (inr A B C s'))
  exact existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    ((continuous_toCompletionLoc Q _ _ S'' hden'').comp (continuous_inl A B C)).continuousAt hu
    fun t ht ↦ isPowerBounded_toCompletionLoc_mul_unit_inv Q _ _ S'' hden'' rfl hu
      (Finset.mul_mem_mul (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))
        (Finset.mem_insert_self _ _))

/-- `C → D → D⟨T''/s''⟩` extends to `C⟨T'/s'⟩`. -/
private theorem existsUnique_rightLoc :
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∃! g : Completion S' →+* Completion S'', Continuous g ∧
      g.comp (toCompletionLoc P' T' s' S' hden') =
        (toCompletionLoc Q _ _ S'' hden'').comp (inr A B C) := by
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  have hu := isUnit_toCompletionLoc_of_dvd Q _ _ S'' hden''
    (dvd_mul_left (inr A B C s') (inl A B C s))
  exact existsUnique_continuous_ringHom_completion_locTopology P' T' s' S' hden'
    ((continuous_toCompletionLoc Q _ _ S'' hden'').comp (continuous_inr A B C)).continuousAt hu
    fun t' ht' ↦ isPowerBounded_toCompletionLoc_mul_unit_inv Q _ _ S'' hden'' (mul_comm _ _) hu
      (by
        rw [Finset.mem_coe, mul_comm (inr A B C t')]
        exact Finset.mul_mem_mul (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht')))

/-- The extension `B⟨T/s⟩ → D⟨T''/s''⟩` of `B → D → D⟨T''/s''⟩`. -/
private noncomputable def leftLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Completion S →+* Completion S'' :=
  (existsUnique_leftLoc P T s S hden T' s' Q S'' hden'').choose

private theorem continuous_leftLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (leftLoc P T s S hden T' s' Q S'' hden'') :=
  (existsUnique_leftLoc P T s S hden T' s' Q S'' hden'').choose_spec.1.1

private theorem leftLoc_comp_toCompletionLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (leftLoc P T s S hden T' s' Q S'' hden'').comp (toCompletionLoc P T s S hden) =
      (toCompletionLoc Q _ _ S'' hden'').comp (inl A B C) :=
  (existsUnique_leftLoc P T s S hden T' s' Q S'' hden'').choose_spec.1.2

/-- The extension `C⟨T'/s'⟩ → D⟨T''/s''⟩` of `C → D → D⟨T''/s''⟩`. -/
private noncomputable def rightLoc :
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Completion S' →+* Completion S'' :=
  (existsUnique_rightLoc T s P' T' s' S' hden' Q S'' hden'').choose

private theorem continuous_rightLoc :
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (rightLoc T s P' T' s' S' hden' Q S'' hden'') :=
  (existsUnique_rightLoc T s P' T' s' S' hden' Q S'' hden'').choose_spec.1.1

private theorem rightLoc_comp_toCompletionLoc :
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (rightLoc T s P' T' s' S' hden' Q S'' hden'').comp (toCompletionLoc P' T' s' S' hden') =
      (toCompletionLoc Q _ _ S'' hden'').comp (inr A B C) :=
  (existsUnique_rightLoc T s P' T' s' S' hden' Q S'' hden'').choose_spec.1.2

/-- The forward map `B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩ → D⟨T''/s''⟩`. -/
private noncomputable def toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    CompletedTensor A (Completion S) (Completion S') →+* Completion S'' :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  lift (leftLoc P T s S hden T' s' Q S'' hden'') (rightLoc T s P' T' s' S' hden' Q S'' hden'')
    (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc,
        leftLoc_comp_toCompletionLoc P T s S hden T' s' Q S'' hden'', RingHom.comp_assoc,
        inl_comp_algebraMap, ← RingHom.comp_assoc,
        ← rightLoc_comp_toCompletionLoc T s P' T' s' S' hden' Q S'' hden'', RingHom.comp_assoc])
    (continuous_leftLoc P T s S hden T' s' Q S'' hden'')
    (continuous_rightLoc T s P' T' s' S' hden' Q S'' hden'')

private theorem leftLoc_toCompletionLoc (b : B) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    leftLoc P T s S hden T' s' Q S'' hden'' (toCompletionLoc P T s S hden b) =
      toCompletionLoc Q _ _ S'' hden'' (inl A B C b) :=
  RingHom.congr_fun (leftLoc_comp_toCompletionLoc P T s S hden T' s' Q S'' hden'') b

private theorem rightLoc_toCompletionLoc (c : C) :
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    rightLoc T s P' T' s' S' hden' Q S'' hden'' (toCompletionLoc P' T' s' S' hden' c) =
      toCompletionLoc Q _ _ S'' hden'' (inr A B C c) :=
  RingHom.congr_fun (rightLoc_comp_toCompletionLoc T s P' T' s' S' hden' Q S'' hden'') c

private theorem continuous_toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (toLoc P T s S hden P' T' s' S' hden' Q S'' hden'') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  exact continuous_lift _ _ _ _ _

private theorem toLoc_inl :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∀ x : Completion S,
      toLoc P T s S hden P' T' s' S' hden' Q S'' hden'' (inl A (Completion S) (Completion S') x) =
        leftLoc P T s S hden T' s' Q S'' hden'' x := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  exact lift_inl _ _ _ _ _

private theorem toLoc_inr :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∀ x : Completion S',
      toLoc P T s S hden P' T' s' S' hden' Q S'' hden'' (inr A (Completion S) (Completion S') x) =
        rightLoc T s P' T' s' S' hden' Q S'' hden'' x := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  exact lift_inr _ _ _ _ _

/-! ### The map `D⟨T''/s''⟩ → B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` -/

/-- `D → B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` extends to `D⟨T''/s''⟩`: the denominator becomes the unit
`s ⊗ s'`, and the fraction of `inl(t) · inr(s')` is `(t/s) ⊗ 1`, the image of a power-bounded
element under the adic coprojection (symmetrically for `inr(t') · inl(s)`). -/
private theorem existsUnique_ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∃! g : Completion S'' →+* CompletedTensor A (Completion S) (Completion S'), Continuous g ∧
      g.comp (toCompletionLoc Q _ _ S'' hden'') =
        map (RingHom.id A) (toCompletionLoc P T s S hden) (toCompletionLoc P' T' s' S' hden')
          rfl rfl (continuous_toCompletionLoc P T s S hden)
          (continuous_toCompletionLoc P' T' s' S' hden') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have hs := isUnit_toCompletionLoc_of_dvd P T s S hden (dvd_refl s)
  have hs' := isUnit_toCompletionLoc_of_dvd P' T' s' S' hden' (dvd_refl s')
  set f := map (RingHom.id A) (toCompletionLoc P T s S hden) (toCompletionLoc P' T' s' S' hden')
    rfl rfl (continuous_toCompletionLoc P T s S hden)
    (continuous_toCompletionLoc P' T' s' S' hden') with hf
  have hu : IsUnit (f (inl A B C s * inr A B C s')) := by
    rw [map_mul, hf, map_inl, map_inr]
    exact (hs.map _).mul (hs'.map _)
  -- every numerator of the left factor is a power-bounded multiple of the image of `inl(s)`
  have hleft : ∀ a ∈ insert (inl A B C s) (T.image (inl A B C)), ∃ y, IsPowerBounded y ∧
      f a = y * f (inl A B C s) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨1, isPowerBounded_one, (one_mul _).symm⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨inl A (Completion S) (Completion S') (toCompletionLoc P T s S hden t * ↑hs.unit⁻¹),
      (isAdicHom_inl _ _ _).isPowerBounded_map
        (isPowerBounded_toCompletionLoc_mul_unit_inv P T s S hden (mul_one s).symm hs
          ((mul_one t).symm ▸ ht)), ?_⟩
    rw [hf, map_inl, map_inl, ← map_mul, mul_assoc, hs.val_inv_mul, mul_one]
  have hright : ∀ b ∈ insert (inr A B C s') (T'.image (inr A B C)), ∃ z, IsPowerBounded z ∧
      f b = z * f (inr A B C s') := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨1, isPowerBounded_one, (one_mul _).symm⟩
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hb
    refine ⟨inr A (Completion S) (Completion S')
        (toCompletionLoc P' T' s' S' hden' t' * ↑hs'.unit⁻¹),
      (isAdicHom_inr _ _ _).isPowerBounded_map
        (isPowerBounded_toCompletionLoc_mul_unit_inv P' T' s' S' hden' (mul_one s').symm hs'
          ((mul_one t').symm ▸ ht')), ?_⟩
    rw [hf, map_inr, map_inr, ← map_mul, mul_assoc, hs'.val_inv_mul, mul_one]
  refine existsUnique_continuous_ringHom_completion_locTopology Q _ _ S'' hden''
    (continuous_map ..).continuousAt hu fun x hx ↦ ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
  obtain ⟨y, hy, hay⟩ := hleft a ha
  obtain ⟨z, hz, hbz⟩ := hright b hb
  have key : f (a * b) * ↑hu.unit⁻¹ = y * z := by
    rw [Units.mul_inv_eq_iff_eq_mul, IsUnit.unit_spec, map_mul, map_mul, hay, hbz]
    ring
  rw [key]
  exact hy.mul hz

/-- The inverse map `D⟨T''/s''⟩ → B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩`. -/
private noncomputable def ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Completion S'' →+* CompletedTensor A (Completion S) (Completion S') :=
  (existsUnique_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'').choose

private theorem continuous_ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'') :=
  (existsUnique_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'').choose_spec.1.1

private theorem ofLoc_toCompletionLoc (x : CompletedTensor A B C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'' (toCompletionLoc Q _ _ S'' hden'' x) =
      map (RingHom.id A) (toCompletionLoc P T s S hden) (toCompletionLoc P' T' s' S' hden')
        rfl rfl (continuous_toCompletionLoc P T s S hden)
        (continuous_toCompletionLoc P' T' s' S' hden') x :=
  RingHom.congr_fun
    (existsUnique_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'').choose_spec.1.2 x

/-! ### The isomorphism -/

private theorem toLoc_comp_ofLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (toLoc P T s S hden P' T' s' S' hden' Q S'' hden'').comp
      (ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'') = RingHom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  refine eq_id_of_comp_toCompletionLoc_eq_self Q _ _ S'' hden'' _
    ((continuous_toLoc P T s S hden P' T' s' S' hden' Q S'' hden'').comp
      (continuous_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'')) ?_
  refine hom_ext (((continuous_toLoc P T s S hden P' T' s' S' hden' Q S'' hden'').comp
      (continuous_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'')).comp
      (continuous_toCompletionLoc Q _ _ S'' hden'')) (continuous_toCompletionLoc Q _ _ S'' hden'')
    (RingHom.ext fun b ↦ ?_) (RingHom.ext fun c ↦ ?_)
  · simp only [RingHom.comp_apply, ofLoc_toCompletionLoc, map_inl, toLoc_inl,
      leftLoc_toCompletionLoc]
  · simp only [RingHom.comp_apply, ofLoc_toCompletionLoc, map_inr, toLoc_inr,
      rightLoc_toCompletionLoc]

private theorem ofLoc_comp_toLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'').comp
      (toLoc P T s S hden P' T' s' S' hden' Q S'' hden'') = RingHom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  have hc := (continuous_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'').comp
    (continuous_toLoc P T s S hden P' T' s' S' hden' Q S'' hden'')
  refine hom_ext hc continuous_id ?_ ?_
  · refine completion_locTopology_ringHom_ext_of_continuous P T s S hden _ _
      (hc.comp (continuous_inl _ _ _)) (continuous_id.comp (continuous_inl _ _ _))
      (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.id_apply, toLoc_inl, leftLoc_toCompletionLoc,
      ofLoc_toCompletionLoc, map_inl]
  · refine completion_locTopology_ringHom_ext_of_continuous P' T' s' S' hden' _ _
      (hc.comp (continuous_inr _ _ _)) (continuous_id.comp (continuous_inr _ _ _))
      (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.id_apply, toLoc_inr, rightLoc_toCompletionLoc,
      ofLoc_toCompletionLoc, map_inr]

/-- **Completed localisations commute with completed tensor products.** For adic homomorphisms
`A → B` and `A → C` of Huber rings, the completed tensor product `B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` of
completed localisations is isomorphic to the completed localisation of `D = B ⊗̂_A C` at the
denominator `inl(s) · inr(s')` with the numerators `({inl(s)} ∪ inl(T)) · ({inr(s')} ∪ inr(T'))`.
It sends `b ⊗ 1` and `1 ⊗ c` to the images of `inl(b)` and `inr(c)`, and it is a homeomorphism
(`TauCeti.Huber.CompletedTensor.isHomeomorph_completionLocEquiv`). -/
noncomputable def completionLocEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    CompletedTensor A (Completion S) (Completion S') ≃+* Completion S'' :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  RingEquiv.ofRingHom (toLoc P T s S hden P' T' s' S' hden' Q S'' hden'')
    (ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'')
    (toLoc_comp_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden'')
    (ofLoc_comp_toLoc P T s S hden P' T' s' S' hden' Q S'' hden'')

/-- The isomorphism sends `b ⊗ 1` to the image of `inl(b)`. -/
@[simp] theorem completionLocEquiv_inl_toCompletionLoc (b : B) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
        (inl A (Completion S) (Completion S') (algebraMap B S b : Completion S)) =
      (algebraMap (CompletedTensor A B C) S'' (inl A B C b) : Completion S'') := by
  rw [← toCompletionLoc_apply P T s S hden, ← toCompletionLoc_apply Q _ _ S'' hden'']
  exact (toLoc_inl P T s S hden P' T' s' S' hden' Q S'' hden'' _).trans
    (leftLoc_toCompletionLoc P T s S hden T' s' Q S'' hden'' b)

/-- The isomorphism sends `1 ⊗ c` to the image of `inr(c)`. -/
@[simp] theorem completionLocEquiv_inr_toCompletionLoc (c : C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
        (inr A (Completion S) (Completion S') (algebraMap C S' c : Completion S')) =
      (algebraMap (CompletedTensor A B C) S'' (inr A B C c) : Completion S'') := by
  rw [← toCompletionLoc_apply P' T' s' S' hden', ← toCompletionLoc_apply Q _ _ S'' hden'']
  exact (toLoc_inr P T s S hden P' T' s' S' hden' Q S'' hden'' _).trans
    (rightLoc_toCompletionLoc T s P' T' s' S' hden' Q S'' hden'' c)

/-- The inverse sends the image of `inl(b)` to `b ⊗ 1`. -/
@[simp] theorem completionLocEquiv_symm_toCompletionLoc_inl (b : B) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
        (algebraMap (CompletedTensor A B C) S'' (inl A B C b) : Completion S'') =
      inl A (Completion S) (Completion S') (algebraMap B S b : Completion S) := by
  rw [← toCompletionLoc_apply P T s S hden, ← toCompletionLoc_apply Q _ _ S'' hden'']
  exact (ofLoc_toCompletionLoc P T s S hden P' T' s' S' hden' Q S'' hden'' _).trans
    (by simp only [map_inl])

/-- The inverse sends the image of `inr(c)` to `1 ⊗ c`. -/
@[simp] theorem completionLocEquiv_symm_toCompletionLoc_inr (c : C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
        (algebraMap (CompletedTensor A B C) S'' (inr A B C c) : Completion S'') =
      inr A (Completion S) (Completion S') (algebraMap C S' c : Completion S') := by
  rw [← toCompletionLoc_apply P' T' s' S' hden', ← toCompletionLoc_apply Q _ _ S'' hden'']
  exact (ofLoc_toCompletionLoc P T s S hden P' T' s' S' hden' Q S'' hden'' _).trans
    (by simp only [map_inr])

/-- The isomorphism is continuous. -/
@[fun_prop] theorem continuous_completionLocEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'') :=
  continuous_toLoc P T s S hden P' T' s' S' hden' Q S'' hden''

/-- The inverse isomorphism is continuous. -/
@[fun_prop] theorem continuous_completionLocEquiv_symm :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    Continuous (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm :=
  continuous_ofLoc P T s S hden P' T' s' S' hden' Q S'' hden''

/-- **`B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` is `D⟨T''/(inl(s) · inr(s'))⟩` as a topological ring.** -/
theorem isHomeomorph_completionLocEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    IsHomeomorph (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'') :=
  (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'',
      continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden''⟩

end TauCeti.Huber.CompletedTensor
