/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.BaseChange
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Pair
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Rational localisations and adic spectra of completed tensor products

Let `f : (A, A⁺) → (B, B⁺)` and `g : (A, A⁺) → (C, C⁺)` be adic morphisms of Huber pairs, let
`(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` be their completed tensor product, and let
`p_B : Spa(D, D⁺) → Spa(B, B⁺)` and `p_C : Spa(D, D⁺) → Spa(C, C⁺)` be the maps induced by the
coprojections `inl` and `inr`. Given rational subsets `W = R(T₀/s₀) ⊆ Spa(A, A⁺)`,
`U = R(T/s) ⊆ Spa(B, B⁺)` and `V = R(T'/s') ⊆ Spa(C, C⁺)` with `Spa(f)(U) ⊆ W` and
`Spa(g)(V) ⊆ W`, this file establishes the three comparisons linking rational localisations with
completed tensor products on adic spectra without completeness, Hausdorffness or sheafiness
hypotheses on `(A, A⁺)`, `(B, B⁺)` or `(C, C⁺)`:

1. **Rational preimages and intersections** (`completedTensorRationalEquiv_preimage` and its
   unbundled components): `p_B⁻¹(U) = R(inl(T)/inl(s))` and `p_C⁻¹(V) = R(inr(T')/inr(s'))` belong
   to `spaRationalFamily`, and `p_B⁻¹(U) ∩ p_C⁻¹(V)` is the rational subset
   `R((insert (inl s) (inl T) * insert (inr s') (inr T')) / (inl s * inr s'))` with open numerator
   ideal.
2. **Comparison of completed rational-localisation pairs** (`completedTensor.rationalRingEquiv` and
   `completedTensor.map_plus_rationalRingEquiv`): along the adic localised morphisms `O(W) → O(U)`
   and `O(W) → O(V)` from `pairHomOfSpaComapImageSubset`, for any presentation `d` of
   `p_B⁻¹(U) ∩ p_C⁻¹(V)` on `D`, `O(U) ⊗̂_{O(W)} O(V)` is canonically isomorphic as a topological
   ring and Huber pair to `O_D(d)`, sending `ρ_B(b) ⊗ₜ ρ_C(c)` to `ρ_D(b ⊗ₜ c)`.
3. **Homeomorphism and rational-subset bijection on adic spectra**
   (`completedTensor.rationalSpaHomeomorph` and `completedTensorRationalEquiv`): pulling valuations
   back along `e⁻¹ ∘ ρ_D` gives a homeomorphism
   `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))` whose preimage map bijects rational subsets
   of `Spa(D, D⁺)` contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily` of
   `Spa(O(U) ⊗̂_{O(W)} O(V))`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.interPresentation`: the canonical presentation of
  `p_B⁻¹(U) ∩ p_C⁻¹(V)` on `B ⊗̂_A C`.
* `TauCeti.Huber.Pair.completedTensor.rationalRingEquiv`: the topological ring equivalence
  `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)` for any presentation `d` of `p_B⁻¹(U) ∩ p_C⁻¹(V)`.
* `TauCeti.Huber.Pair.completedTensor.rationalSpaHomeomorph`: the induced homeomorphism
  `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`.

## Main results

* `TauCeti.Huber.Pair.completedTensorRationalEquiv_preimage`: preimage, rationality and
  intersection formulas for rational subsets on `Spa((B, B⁺) ⊗̂_A (C, C⁺))`.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv`: assembly of the adic base-change morphisms
  `O(W) → O(U)` and `O(W) → O(V)`, the topological Huber-pair equivalence `e`, and the `Spa`
  homeomorphism `H` matching rational subsets.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §1, Lemma 1.5(ii) and §3, Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.5, Lemma 7.46(3) and §8.1,
  Lemma 8.1 and Proposition 8.2.
-/

public section

open UniformSpace TensorProduct

namespace TauCeti.Huber.Pair

open CompletedTensor PairOfDefinition ValuationSpectrum
open scoped Pointwise

section Preimage

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

open Classical in
/-- Preimage of a rational subset `R(T/s) ⊆ Spa(B, B⁺)` under the left projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_spaComap_preimage_rationalSubset (UB : Pair B) (UC : Pair C)
    (T : Finset B) (s : B) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C s) := by
  simpa only [completedTensor.toRingHom_inl] using
    (completedTensor.inl A UB UC).spaComap_preimage_rationalSubset T s

open Classical in
/-- Preimage of a rational subset `R(T'/s') ⊆ Spa(C, C⁺)` under the right projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inr_spaComap_preimage_rationalSubset (UB : Pair B) (UC : Pair C)
    (T' : Finset C) (s' : C) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T'.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C s') := by
  simpa only [completedTensor.toRingHom_inr] using
    (completedTensor.inr A UB UC).spaComap_preimage_rationalSubset T' s'

open Classical in
/-- Intersection of the preimages of `R(T/s) ⊆ Spa(B, B⁺)` and `R(T'/s') ⊆ Spa(C, C⁺)` inside
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_rationalSubset (UB : Pair B) (UC : Pair C)
    (T : Finset B) (s : B) (T' : Finset C) (s' : C) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') := by
  rw [completedTensor.inl_spaComap_preimage_rationalSubset,
    completedTensor.inr_spaComap_preimage_rationalSubset, ← Set.preimage_inter,
    rationalSubset_inter]

/-- Preimage of a member of `spaRationalFamily UB.plus` along `(inl A UB UC).spaComap` belongs to
`spaRationalFamily` of the completed tensor pair (Wedhorn, Lemma 7.46(3)). -/
theorem completedTensor.inl_spaComap_preimage_mem_spaRationalFamily (UB : Pair B) (UC : Pair C)
    {U : Set (spa UB.plus)} (hU : U ∈ spaRationalFamily UB.plus) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' U ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun J hJ ↦ by
      simpa only [completedTensor.toRingHom_inl] using
        (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage of a member of `spaRationalFamily UC.plus` along `(inr A UB UC).spaComap` belongs to
`spaRationalFamily` of the completed tensor pair (Wedhorn, Lemma 7.46(3)). -/
theorem completedTensor.inr_spaComap_preimage_mem_spaRationalFamily (UB : Pair B) (UC : Pair C)
    {V : Set (spa UC.plus)} (hV : V ∈ spaRationalFamily UC.plus) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' V ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun J hJ ↦ by
      simpa only [completedTensor.toRingHom_inr] using
        (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

omit [IsHuberRing B] [IsHuberRing C] in
open Classical in
/-- When `T · B` and `T' · C` are open ideals, the intersection numerator finset
`insert (inl s) (inl T) * insert (inr s') (inr T')` generates an open ideal in `B ⊗̂_A C`. -/
theorem completedTensor.isOpen_span_inl_mul_inr {T : Finset B} {s : B} {T' : Finset C} {s' : C}
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    IsOpen (Ideal.span
      ((insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
        insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) :
          Finset (CompletedTensor A B C)) : Set (CompletedTensor A B C)) :
      Set (CompletedTensor A B C)) := by
  obtain ⟨PD⟩ := IsHuberRing.nonempty_pairOfDefinition (A := CompletedTensor A B C)
  have hTl : IsOpen (Ideal.span
      ((T.image (CompletedTensor.inl A B C) : Finset (CompletedTensor A B C)) :
        Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hT
  have hTr : IsOpen (Ideal.span
      ((T'.image (CompletedTensor.inr A B C) : Finset (CompletedTensor A B C)) :
        Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hT'
  exact PD.isOpen_span_insert_mul_insert hTl hTr

/-- Intersection of the preimages of two rational subsets with open numerator ideals belongs to
`spaRationalFamily` of the completed tensor pair. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_mem_spaRationalFamily
    (UB : Pair B) (UC : Pair C) {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus T' s') ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  classical
  exact mem_spaRationalFamily_iff.mpr
    ⟨_, _, completedTensor.isOpen_span_inl_mul_inr hT hT',
      completedTensor.inl_preimage_inter_inr_preimage_rationalSubset UB UC T s T' s'⟩

open Classical in
/-- **The canonical presentation of `p_B⁻¹(R(T/s)) ∩ p_C⁻¹(R(T'/s'))`** with respect to a pair of
definition `PD` on `B ⊗̂_A C`, when `T · B` and `T' · C` are open ideals. -/
noncomputable def completedTensor.interPresentation
    (PD : PairOfDefinition (CompletedTensor A B C)) {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    PD.Presentation where
  num := insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
    insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C))
  den := CompletedTensor.inl A B C s * CompletedTensor.inr A B C s'
  hasDenominatorPower := CompletedTensor.hasDenominatorPower_inl_mul_inr PD hT hT' _

omit [IsHuberRing B] [IsHuberRing C] in
open Classical in
/-- Numerator finset of `completedTensor.interPresentation`. -/
@[simp]
theorem completedTensor.interPresentation_num
    (PD : PairOfDefinition (CompletedTensor A B C)) {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    (completedTensor.interPresentation PD s s' hT hT').num =
      insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
        insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) := (rfl)

omit [IsHuberRing B] [IsHuberRing C] in
/-- Denominator of `completedTensor.interPresentation`. -/
@[simp]
theorem completedTensor.interPresentation_den
    (PD : PairOfDefinition (CompletedTensor A B C)) {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    (completedTensor.interPresentation PD s s' hT hT').den =
      CompletedTensor.inl A B C s * CompletedTensor.inr A B C s' := (rfl)

open Classical in
/-- **Rational preimages and intersections on completed tensor products** (Wedhorn, Lemma 7.46(3)
and Remark 7.30(5)): without assuming sheafiness or completeness, `p_B⁻¹(R(T/s))` and
`p_C⁻¹(R(T'/s'))` are rational subsets of `Spa((B, B⁺) ⊗̂_A (C, C⁺))`, and their intersection is the
rational subset `R((insert (inl s) (inl T) * insert (inr s') (inr T')) / (inl s * inr s'))` with
open numerator ideal. -/
theorem completedTensorRationalEquiv_preimage (UB : Pair B) (UC : Pair C)
    {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    let U : Set (spa UB.plus) := Subtype.val ⁻¹' rationalSubset UB.plus T s
    let V : Set (spa UC.plus) := Subtype.val ⁻¹' rationalSubset UC.plus T' s'
    let pB := (completedTensor.inl A UB UC).spaComap
    let pC := (completedTensor.inr A UB UC).spaComap
    (pB ⁻¹' U = Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C s) ∧
      pB ⁻¹' U ∈ spaRationalFamily (UB.completedTensor A UC).plus) ∧
    (pC ⁻¹' V = Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T'.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C s') ∧
      pC ⁻¹' V ∈ spaRationalFamily (UB.completedTensor A UC).plus) ∧
    (pB ⁻¹' U ∩ pC ⁻¹' V = Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') ∧
      pB ⁻¹' U ∩ pC ⁻¹' V ∈ spaRationalFamily (UB.completedTensor A UC).plus) :=
  ⟨⟨completedTensor.inl_spaComap_preimage_rationalSubset UB UC T s,
      completedTensor.inl_spaComap_preimage_mem_spaRationalFamily UB UC
        (mem_spaRationalFamily_iff.mpr ⟨T, s, hT, rfl⟩)⟩,
    ⟨completedTensor.inr_spaComap_preimage_rationalSubset UB UC T' s',
      completedTensor.inr_spaComap_preimage_mem_spaRationalFamily UB UC
        (mem_spaRationalFamily_iff.mpr ⟨T', s', hT', rfl⟩)⟩,
    ⟨completedTensor.inl_preimage_inter_inr_preimage_rationalSubset UB UC T s T' s',
      completedTensor.inl_preimage_inter_inr_preimage_mem_spaRationalFamily UB UC s s' hT hT'⟩⟩

/-- Degenerate case `U = Spa(B, B⁺)` (`T = {1}`, `s = 1`): intersecting with `p_B⁻¹(R({1}/1))`
leaves `p_C⁻¹(V)` unchanged. -/
theorem completedTensor.inl_preimage_singleton_one_inter (UB : Pair B) (UC : Pair C)
    (V : Set (spa UC.plus)) :
    (completedTensor.inl A UB UC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset UB.plus {1} 1) ∩
      (completedTensor.inr A UB UC).spaComap ⁻¹' V =
      (completedTensor.inr A UB UC).spaComap ⁻¹' V := by
  rw [rationalSubset_singleton_one, Subtype.coe_preimage_self, Set.preimage_univ, Set.univ_inter]

/-- Degenerate case `s = 0`: `p_B⁻¹(R(T/0)) ∩ p_C⁻¹(R(T'/s'))` is empty. -/
theorem completedTensor.inl_preimage_zero_inter_inr_preimage (UB : Pair B) (UC : Pair C)
    (T : Finset B) (T' : Finset C) (s' : C) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T 0) ∩
      (completedTensor.inr A UB UC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset UC.plus T' s') = ∅ := by
  ext x
  simp

omit [IsHuberRing B] [IsHuberRing C] in
open Classical in
/-- Degenerate case `s = 0`: the completed rational localisation of `B ⊗̂_A C` at
`completedTensor.interPresentation PD 0 s' hT hT'` is trivial (`Subsingleton`). -/
theorem completedTensor.subsingleton_completion_interPresentation_zero
    (PD : PairOfDefinition (CompletedTensor A B C)) {T : Finset B} {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    let d₀ := completedTensor.interPresentation PD (T := T) 0 (T' := T') s' hT hT'
    letI := locUniformSpace PD d₀.num d₀.den _ d₀.hasDenominatorPower
    Subsingleton (Completion (Localization.Away d₀.den)) := by
  intro d₀
  let _ := locUniformSpace PD d₀.num d₀.den _ d₀.hasDenominatorPower
  have hS : Subsingleton (Localization.Away d₀.den) :=
    IsLocalization.subsingleton (M := Submonoid.powers d₀.den) ⟨1, by simp [d₀]⟩
  exact subsingleton_of_zero_eq_one <| by
    simpa only [Completion.coe_zero, Completion.coe_one] using
      congrArg (fun x : Localization.Away d₀.den ↦ (x : Completion (Localization.Away d₀.den)))
        (Subsingleton.elim 0 1)

end Preimage

section RationalEquiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Topological ring isomorphism `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)`** for presentations `a`, `b`,
`c` of `W ⊆ Spa(A, A⁺)`, `U ⊆ Spa(B, B⁺)`, `V ⊆ Spa(C, C⁺)` with `Spa(f)(U) ⊆ W`, `Spa(g)(V) ⊆ W`,
and any presentation `d` on `D = B ⊗̂_A C` representing `p_B⁻¹(U) ∩ p_C⁻¹(V)`. -/
noncomputable def completedTensor.rationalRingEquiv
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C)) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    CompletedTensor (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))
      (Completion (Localization.Away c.den)) ≃+* Completion (Localization.Away d.den) :=
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ := ((toCompletionLoc PB b.num b.den _ b.hasDenominatorPower).comp
    (algebraMap A B)).toAlgebra
  let _ := ((toCompletionLoc PC c.num c.den _ c.hasDenominatorPower).comp
    (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away b.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PB b.num b.den _ b.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away c.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PC c.num c.den _ c.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := Classical.decEq (CompletedTensor A B C)
  let num₀ : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C b.den) (b.num.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C c.den) (c.num.image (CompletedTensor.inr A B C))
  let den₀ : CompletedTensor A B C :=
    CompletedTensor.inl A B C b.den * CompletedTensor.inr A B C c.den
  let hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr PD (s := b.den) (s' := c.den)
    hb hc (Localization.Away den₀)
  let _ := locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isUniformAddGroup_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isTopologicalRing_locUniformSpace PD num₀ den₀ _ hden₀
  ((completionLocBaseEquiv PA a.num a.den _ a.hasDenominatorPower _ _
      (pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf).continuous_toRingHom
      (pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg).continuous_toRingHom
      (by rw [toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc, hf_alg]; rfl)
      (by rw [toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc, hg_alg]; rfl)).trans
    (completionLocEquiv PB b.num b.den _ b.hasDenominatorPower
      PC c.num c.den _ c.hasDenominatorPower PD _ hden₀)).trans
    (presentationRingEquivOfEq PD (UB.completedTensor A UC).plus
      (UB.completedTensor A UC).isRingOfIntegralElements.isPowerBounded_of_mem
      num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower
      (rationalSubset_eq_of_val_preimage_eq <|
        (completedTensor.inl_preimage_inter_inr_preimage_rationalSubset UB UC b.num b.den
          c.num c.den).symm.trans hd.symm))

/-- `completedTensor.rationalRingEquiv` is continuous. -/
theorem completedTensor.continuous_rationalRingEquiv
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C)) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    Continuous (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd) := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ := ((toCompletionLoc PB b.num b.den _ b.hasDenominatorPower).comp
    (algebraMap A B)).toAlgebra
  let _ := ((toCompletionLoc PC c.num c.den _ c.hasDenominatorPower).comp
    (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away b.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PB b.num b.den _ b.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away c.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PC c.num c.den _ c.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := Classical.decEq (CompletedTensor A B C)
  let num₀ : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C b.den) (b.num.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C c.den) (c.num.image (CompletedTensor.inr A B C))
  let den₀ : CompletedTensor A B C :=
    CompletedTensor.inl A B C b.den * CompletedTensor.inr A B C c.den
  let hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr PD (s := b.den) (s' := c.den)
    hb hc (Localization.Away den₀)
  let _ := locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isUniformAddGroup_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isTopologicalRing_locUniformSpace PD num₀ den₀ _ hden₀
  dsimp only [completedTensor.rationalRingEquiv]
  rw [RingEquiv.coe_trans, RingEquiv.coe_trans]
  exact (continuous_presentationRingEquivOfEq PD (UB.completedTensor A UC).plus _
      num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _).comp
    ((continuous_completionLocEquiv PB b.num b.den _ b.hasDenominatorPower
        PC c.num c.den _ c.hasDenominatorPower PD _ hden₀).comp
      (continuous_completionLocBaseEquiv PA a.num a.den _ a.hasDenominatorPower _ _ _ _ _ _))

/-- The inverse of `completedTensor.rationalRingEquiv` is continuous. -/
theorem completedTensor.continuous_rationalRingEquiv_symm
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C)) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    Continuous (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd).symm := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ := ((toCompletionLoc PB b.num b.den _ b.hasDenominatorPower).comp
    (algebraMap A B)).toAlgebra
  let _ := ((toCompletionLoc PC c.num c.den _ c.hasDenominatorPower).comp
    (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away b.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PB b.num b.den _ b.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away c.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PC c.num c.den _ c.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := Classical.decEq (CompletedTensor A B C)
  let num₀ : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C b.den) (b.num.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C c.den) (c.num.image (CompletedTensor.inr A B C))
  let den₀ : CompletedTensor A B C :=
    CompletedTensor.inl A B C b.den * CompletedTensor.inr A B C c.den
  let hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr PD (s := b.den) (s' := c.den)
    hb hc (Localization.Away den₀)
  let _ := locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isUniformAddGroup_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isTopologicalRing_locUniformSpace PD num₀ den₀ _ hden₀
  dsimp only [completedTensor.rationalRingEquiv]
  rw [RingEquiv.symm_trans, RingEquiv.symm_trans, RingEquiv.coe_trans, RingEquiv.coe_trans]
  exact ((continuous_completionLocBaseEquiv_symm PA a.num a.den _ a.hasDenominatorPower _ _ _ _ _
      _).comp
    (continuous_completionLocEquiv_symm PB b.num b.den _ b.hasDenominatorPower
      PC c.num c.den _ c.hasDenominatorPower PD _ hden₀)).comp
    (continuous_presentationRingEquivOfEq_symm PD (UB.completedTensor A UC).plus _
      num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _)

/-- `completedTensor.rationalRingEquiv` is a homeomorphism. -/
theorem completedTensor.isHomeomorph_rationalRingEquiv
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C)) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    IsHomeomorph (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd) :=
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  let _ := f₀.toRingHom.toAlgebra
  let _ := g₀.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away c.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
    hf_alg hg_alg hf hg hd).toEquiv.isHomeomorph_iff.mpr
    ⟨completedTensor.continuous_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd,
      completedTensor.continuous_rationalRingEquiv_symm PA UA hPA a PB UB hPB b hb PC UC hPC c hc
        PD d f g hf_alg hg_alg hf hg hd⟩

/-- `completedTensor.rationalRingEquiv` carries the completed tensor plus ring of `O(U)` and
`O(V)` over `O(W)` onto `completedPlusSubring` of `d`. -/
theorem completedTensor.map_plus_rationalRingEquiv
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C))
    (hPD : PD.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    (((rationalLocalizationPair PB UB hPB b.num b.den _ b.hasDenominatorPower).completedTensor
        (Completion (Localization.Away a.den))
        (rationalLocalizationPair PC UC hPC c.num c.den _ c.hasDenominatorPower)).plus.map
      (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd : _ →+* _)) =
      completedPlusSubring PD (UB.completedTensor A UC).plus d.num d.den _
        d.hasDenominatorPower := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ := ((toCompletionLoc PB b.num b.den _ b.hasDenominatorPower).comp
    (algebraMap A B)).toAlgebra
  let _ := ((toCompletionLoc PC c.num c.den _ c.hasDenominatorPower).comp
    (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away b.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PB b.num b.den _ b.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away c.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PC c.num c.den _ c.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := Classical.decEq (CompletedTensor A B C)
  let num₀ : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C b.den) (b.num.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C c.den) (c.num.image (CompletedTensor.inr A B C))
  let den₀ : CompletedTensor A B C :=
    CompletedTensor.inl A B C b.den * CompletedTensor.inr A B C c.den
  let hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr PD (s := b.den) (s' := c.den)
    hb hc (Localization.Away den₀)
  let _ := locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isUniformAddGroup_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isTopologicalRing_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isHuberRing_completion_locTopology PD num₀ den₀ _ hden₀
  dsimp only [completedTensor.rationalRingEquiv]
  rw [← RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_trans', RingEquiv.toRingHom_trans',
    ← Subring.map_map, ← Subring.map_map,
    completedTensor.map_plus_completionLocBaseEquiv PA a.num a.den _ a.hasDenominatorPower,
    completedTensor.map_plus_completionLocEquiv PB UB b.num b.den _ b.hasDenominatorPower
      PC UC c.num c.den _ c.hasDenominatorPower PD _ hden₀ hPB hPC hPD,
    rationalLocalizationPair_plus]
  exact map_completedPlusSubring_presentationRingEquivOfEq PD (UB.completedTensor A UC).plus
    (fun j _ ↦ hPD j.2)
    (UB.completedTensor A UC).isRingOfIntegralElements.isPowerBounded_of_mem
    num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _

/-- **Pure-tensor coefficient formula for `completedTensor.rationalRingEquiv`**:
`e(ρ_B(x) ⊗ₜ ρ_C(y)) = ρ_D(x ⊗ₜ y)`. -/
theorem completedTensor.rationalRingEquiv_toCompletion_tmul
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C)) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den))
    (x : B) (y : C) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd
        (CompletedTensor.toCompletion (Completion (Localization.Away a.den))
          (Completion (Localization.Away b.den)) (Completion (Localization.Away c.den))
          (toCompletionLoc PB b.num b.den _ b.hasDenominatorPower x ⊗ₜ
            toCompletionLoc PC c.num c.den _ c.hasDenominatorPower y)) =
      toCompletionLoc PD d.num d.den _ d.hasDenominatorPower
        (CompletedTensor.toCompletion A B C (x ⊗ₜ y)) := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ := ((toCompletionLoc PB b.num b.den _ b.hasDenominatorPower).comp
    (algebraMap A B)).toAlgebra
  let _ := ((toCompletionLoc PC c.num c.den _ c.hasDenominatorPower).comp
    (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away b.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PB b.num b.den _ b.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion (Localization.Away c.den))) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc PC c.num c.den _ c.hasDenominatorPower)
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := Classical.decEq (CompletedTensor A B C)
  let num₀ : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C b.den) (b.num.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C c.den) (c.num.image (CompletedTensor.inr A B C))
  let den₀ : CompletedTensor A B C :=
    CompletedTensor.inl A B C b.den * CompletedTensor.inr A B C c.den
  let hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr PD (s := b.den) (s' := c.den)
    hb hc (Localization.Away den₀)
  let _ := locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isUniformAddGroup_locUniformSpace PD num₀ den₀ _ hden₀
  have _ := isTopologicalRing_locUniformSpace PD num₀ den₀ _ hden₀
  dsimp only [completedTensor.rationalRingEquiv]
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, completionLocBaseEquiv_toCompletion_tmul,
    completionLocEquiv_toCompletion_tmul]
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using
    RingHom.congr_fun
      (presentationRingEquivOfEq_coe_comp_toCompletionLoc PD (UB.completedTensor A UC).plus _
        num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _) _

/-- **Homeomorphism `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`** pulling valuations back
along `e⁻¹ ∘ ρ_D` (Huber 1994, Lemma 1.5(ii); Wedhorn, Proposition 8.2(2)). -/
noncomputable def completedTensor.rationalSpaHomeomorph
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C))
    (hPD : PD.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    spa ((rationalLocalizationPair PB UB hPB b.num b.den _ b.hasDenominatorPower).completedTensor
        (Completion (Localization.Away a.den))
        (rationalLocalizationPair PC UC hPC c.num c.den _ c.hasDenominatorPower)).plus ≃ₜ
      ↥((completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :=
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  let _ := f₀.toRingHom.toAlgebra
  let _ := g₀.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away c.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  ((spaHomeomorphOfRingEquiv
      (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd)
      (completedTensor.continuous_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
        PD d f g hf_alg hg_alg hf hg hd)
      (completedTensor.continuous_rationalRingEquiv_symm PA UA hPA a PB UB hPB b hb PC UC hPC c hc
        PD d f g hf_alg hg_alg hf hg hd)
      (completedTensor.map_plus_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
        PD hPD d f g hf_alg hg_alg hf hg hd)).trans
    (spaCompletedLocalizationHomeomorph PD (UB.completedTensor A UC).plus hPD d.num d.den _
      d.hasDenominatorPower)).trans
    (Homeomorph.setCongr hd)

/-- `completedTensor.rationalSpaHomeomorph` pulls valuations back along `e.symm ∘ ρ_D`. -/
@[simp]
theorem completedTensor.rationalSpaHomeomorph_val
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C))
    (hPD : PD.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (d : PD.Presentation)
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    ∀ v : spa
        ((rationalLocalizationPair PB UB hPB b.num b.den _ b.hasDenominatorPower).completedTensor
          (Completion (Localization.Away a.den))
          (rationalLocalizationPair PC UC hPC c.num c.den _ c.hasDenominatorPower)).plus,
      ((completedTensor.rationalSpaHomeomorph PA UA hPA a PB UB hPB b hb PC UC hPC c hc
          PD hPD d f g hf_alg hg_alg hf hg hd v).1 : Spv (CompletedTensor A B C)) =
        ValuationSpectrum.comap
          ((completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
              PD d f g hf_alg hg_alg hf hg hd).symm.toRingHom.comp
            (toCompletionLoc PD d.num d.den _ d.hasDenominatorPower)) v.1 := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  let _ := f₀.toRingHom.toAlgebra
  let _ := g₀.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away c.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  dsimp only [completedTensor.rationalSpaHomeomorph]
  intro v
  simp only [Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, spaComapLoc_val,
    spaHomeomorphOfRingEquiv_val, ← RingEquiv.toRingHom_eq_coe]
  rw [← Function.comp_apply
      (f := ValuationSpectrum.comap (toCompletionLoc PD d.num d.den _ d.hasDenominatorPower)),
    ← ValuationSpectrum.comap_comp]

/-- Preimage under `completedTensor.rationalSpaHomeomorph` bijects rational subsets of `Spa(D, D⁺)`
contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily` of `Spa(O(U) ⊗̂_{O(W)} O(V))`. -/
theorem completedTensor.bijOn_preimage_rationalSpaHomeomorph_spaRationalFamily
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C))
    (hPD : PD.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (d : PD.Presentation)
    (hd_open : IsOpen (Ideal.span (d.num : Set (CompletedTensor A B C)) :
      Set (CompletedTensor A B C)))
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away b.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
        (Completion (Localization.Away c.den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
        PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
    Set.BijOn (fun Z : Set (spa (UB.completedTensor A UC).plus) ↦
        completedTensor.rationalSpaHomeomorph PA UA hPA a PB UB hPB b hb PC UC hPC c hc
          PD hPD d f g hf_alg hg_alg hf hg hd ⁻¹' (Subtype.val ⁻¹' Z))
      {Z ∈ spaRationalFamily (UB.completedTensor A UC).plus |
        Z ⊆ (completedTensor.inl A UB UC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
          (completedTensor.inr A UB UC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)}
      (spaRationalFamily
        ((rationalLocalizationPair PB UB hPB b.num b.den _ b.hasDenominatorPower).completedTensor
          (Completion (Localization.Away a.den))
          (rationalLocalizationPair PC UC hPC c.num c.den _ c.hasDenominatorPower)).plus) := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let f₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  let g₀ := pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
    PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  let _ := f₀.toRingHom.toAlgebra
  let _ := g₀.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf
  have _ : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
      (Completion (Localization.Away c.den))) :=
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg
  dsimp only
  have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily
    (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
      hf_alg hg_alg hf hg hd)
    (completedTensor.continuous_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd)
    (completedTensor.continuous_rationalRingEquiv_symm PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd)
    (completedTensor.map_plus_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD hPD d f g hf_alg hg_alg hf hg hd)
  have hbij₂ := bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily
    PD (UB.completedTensor A UC).plus hPD d.num d.den hd_open _ d.hasDenominatorPower
  have hdom : {W ∈ spaRationalFamily (UB.completedTensor A UC).plus |
        W ⊆ Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den} =
      {Z ∈ spaRationalFamily (UB.completedTensor A UC).plus |
        Z ⊆ (completedTensor.inl A UB UC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
          (completedTensor.inr A UB UC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)} := by
    simp only [hd]
  rw [hdom] at hbij₂
  exact (hbij₁.comp hbij₂).congr fun Z _ ↦ by
    ext x
    simp [completedTensor.rationalSpaHomeomorph]

/-- **Rational localisation commutes with completed tensor products** (Kedlaya–Liu §2.4, after
Definition 2.4.12; Huber 1994, Lemma 1.5(ii) and Proposition 3.7; Wedhorn, Lemma 8.1 and
Proposition 8.2(2)).

Given adic morphisms `f : (A, A⁺) → (B, B⁺)` and `g : (A, A⁺) → (C, C⁺)`, presentations `a`, `b`,
`c` of `W ⊆ Spa(A, A⁺)`, `U ⊆ Spa(B, B⁺)`, `V ⊆ Spa(C, C⁺)` with `Spa(f)(U) ⊆ W` and
`Spa(g)(V) ⊆ W`, and a presentation `d` on `D = B ⊗̂_A C` with open numerator ideal representing
`p_B⁻¹(U) ∩ p_C⁻¹(V)`, there exist:
1. Compatible adic morphisms `f₀ : O(W) → O(U)` and `g₀ : O(W) → O(V)` of rational-localisation
   Huber pairs (`pairHomOfSpaComapImageSubset`),
2. A topological ring equivalence `e : O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)`
   (`completedTensor.rationalRingEquiv`) carrying the completed tensor plus ring onto
   `completedPlusSubring` of `d` and sending `ρ_B(x) ⊗ₜ ρ_C(y)` to `ρ_D(x ⊗ₜ y)`, and
3. A homeomorphism `H : Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`
   (`completedTensor.rationalSpaHomeomorph`) pulling valuations back along `e.symm ∘ ρ_D` whose
   preimage map bijects rational subsets of `Spa(D, D⁺)` contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto
   `spaRationalFamily` of `Spa(O(U) ⊗̂_{O(W)} O(V))`. -/
theorem completedTensorRationalEquiv
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (a : PA.Presentation)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (b : PB.Presentation) (hb : IsOpen (Ideal.span (b.num : Set B) : Set B))
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (c : PC.Presentation) (hc : IsOpen (Ideal.span (c.num : Set C) : Set C))
    (PD : PairOfDefinition (CompletedTensor A B C))
    (hPD : PD.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (d : PD.Presentation)
    (hd_open : IsOpen (Ideal.span (d.num : Set (CompletedTensor A B C)) :
      Set (CompletedTensor A B C)))
    (f : Hom UA UB) (g : Hom UA UC)
    (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hg : g.spaComap '' (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den) ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus a.num a.den)
    (hd : (Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den :
        Set (spa (UB.completedTensor A UC).plus)) =
      (completedTensor.inl A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)) :
    letI := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
    letI := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
    letI := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
    letI := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
    letI := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
    ∃ (f₀ : Hom (rationalLocalizationPair PA UA hPA a.num a.den _ a.hasDenominatorPower)
          (rationalLocalizationPair PB UB hPB b.num b.den _ b.hasDenominatorPower))
      (g₀ : Hom (rationalLocalizationPair PA UA hPA a.num a.den _ a.hasDenominatorPower)
          (rationalLocalizationPair PC UC hPC c.num c.den _ c.hasDenominatorPower))
      (hf₀_adic : IsAdicHom f₀.toRingHom)
      (hg₀_adic : IsAdicHom g₀.toRingHom),
      f₀.comp (toCompletionLocHom PA UA hPA a.num a.den _ a.hasDenominatorPower) =
          (toCompletionLocHom PB UB hPB b.num b.den _ b.hasDenominatorPower).comp f ∧
        g₀.comp (toCompletionLocHom PA UA hPA a.num a.den _ a.hasDenominatorPower) =
          (toCompletionLocHom PC UC hPC c.num c.den _ c.hasDenominatorPower).comp g ∧
        letI := f₀.toRingHom.toAlgebra
        letI := g₀.toRingHom.toAlgebra
        haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
          (Completion (Localization.Away b.den))) := hf₀_adic
        haveI : IsAdicHom (algebraMap (Completion (Localization.Away a.den))
          (Completion (Localization.Away c.den))) := hg₀_adic
        ∃ (e : CompletedTensor (Completion (Localization.Away a.den))
            (Completion (Localization.Away b.den))
            (Completion (Localization.Away c.den)) ≃+* Completion (Localization.Away d.den)),
          IsHomeomorph e ∧
            (((rationalLocalizationPair PB UB hPB b.num b.den _
                  b.hasDenominatorPower).completedTensor
                (Completion (Localization.Away a.den))
                (rationalLocalizationPair PC UC hPC c.num c.den _
                  c.hasDenominatorPower)).plus.map (e : _ →+* _) =
              completedPlusSubring PD (UB.completedTensor A UC).plus d.num d.den _
                d.hasDenominatorPower) ∧
            (∀ (x : B) (y : C),
              e (CompletedTensor.toCompletion (Completion (Localization.Away a.den))
                  (Completion (Localization.Away b.den))
                  (Completion (Localization.Away c.den))
                  (toCompletionLoc PB b.num b.den _ b.hasDenominatorPower x ⊗ₜ
                    toCompletionLoc PC c.num c.den _ c.hasDenominatorPower y)) =
                toCompletionLoc PD d.num d.den _ d.hasDenominatorPower
                  (CompletedTensor.toCompletion A B C (x ⊗ₜ y))) ∧
            ∃ H : spa ((rationalLocalizationPair PB UB hPB b.num b.den _
                  b.hasDenominatorPower).completedTensor
                (Completion (Localization.Away a.den))
                (rationalLocalizationPair PC UC hPC c.num c.den _
                  c.hasDenominatorPower)).plus ≃ₜ
              ↥((completedTensor.inl A UB UC).spaComap ⁻¹'
                  (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
                (completedTensor.inr A UB UC).spaComap ⁻¹'
                  (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)),
              (∀ v, ((H v).1 : Spv (CompletedTensor A B C)) =
                  ValuationSpectrum.comap (e.symm.toRingHom.comp
                    (toCompletionLoc PD d.num d.den _ d.hasDenominatorPower)) v.1) ∧
                Set.BijOn (fun Z : Set (spa (UB.completedTensor A UC).plus) ↦
                    H ⁻¹' (Subtype.val ⁻¹' Z))
                  {Z ∈ spaRationalFamily (UB.completedTensor A UC).plus |
                    Z ⊆ (completedTensor.inl A UB UC).spaComap ⁻¹'
                        (Subtype.val ⁻¹' rationalSubset UB.plus b.num b.den) ∩
                      (completedTensor.inr A UB UC).spaComap ⁻¹'
                        (Subtype.val ⁻¹' rationalSubset UC.plus c.num c.den)}
                  (spaRationalFamily
                    ((rationalLocalizationPair PB UB hPB b.num b.den _
                        b.hasDenominatorPower).completedTensor
                      (Completion (Localization.Away a.den))
                      (rationalLocalizationPair PC UC hPC c.num c.den _
                        c.hasDenominatorPower)).plus) := by
  let _ := locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PA a.num a.den _ a.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PA a.num a.den _ a.hasDenominatorPower
  let _ := locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PB b.num b.den _ b.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PB b.num b.den _ b.hasDenominatorPower
  let _ := locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PC c.num c.den _ c.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology PC c.num c.den _ c.hasDenominatorPower
  let _ := locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace PD d.num d.den _ d.hasDenominatorPower
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  refine ⟨pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf,
    pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg,
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PB UB hPB b.num b.den _ b.hasDenominatorPower f hf,
    isAdicHom_pairHomOfSpaComapImageSubset PA UA hPA a.num a.den _ a.hasDenominatorPower
      PC UC hPC c.num c.den _ c.hasDenominatorPower g hg,
    pairHomOfSpaComapImageSubset_comp_toCompletionLocHom PA UA hPA a.num a.den _
      a.hasDenominatorPower PB UB hPB b.num b.den _ b.hasDenominatorPower f hf,
    pairHomOfSpaComapImageSubset_comp_toCompletionLocHom PA UA hPA a.num a.den _
      a.hasDenominatorPower PC UC hPC c.num c.den _ c.hasDenominatorPower g hg,
    completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
      hf_alg hg_alg hf hg hd,
    completedTensor.isHomeomorph_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd,
    completedTensor.map_plus_rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD hPD d f g hf_alg hg_alg hf hg hd,
    completedTensor.rationalRingEquiv_toCompletion_tmul PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd,
    completedTensor.rationalSpaHomeomorph PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD hPD d f g hf_alg hg_alg hf hg hd,
    completedTensor.rationalSpaHomeomorph_val PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD hPD d f g hf_alg hg_alg hf hg hd,
    completedTensor.bijOn_preimage_rationalSpaHomeomorph_spaRationalFamily
      PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD hPD d hd_open f g hf_alg hg_alg hf hg hd⟩

end RationalEquiv

end TauCeti.Huber.Pair
