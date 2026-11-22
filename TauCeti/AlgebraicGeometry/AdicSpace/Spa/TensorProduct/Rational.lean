/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.BaseChange
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Pair
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Rational localisations and adic spectra of completed tensor products

Let `f : (A, A⁺) → (B, B⁺)` and `g : (A, A⁺) → (C, C⁺)` be adic morphisms of Huber pairs,
`(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` their completed tensor product, and `p_B`, `p_C` the maps on `Spa`
induced by `inl` and `inr`. Given rational subsets `W = R(T₀/s₀) ⊆ Spa(A, A⁺)`,
`U = R(T/s) ⊆ Spa(B, B⁺)` and `V = R(T'/s') ⊆ Spa(C, C⁺)` with `Spa(f)(U) ⊆ W` and
`Spa(g)(V) ⊆ W`, this file establishes (without completeness, Hausdorffness or sheafiness
hypotheses):

1. **Rational preimages and intersections**
   (`completedTensor.inl_spaComap_preimage_rationalSubset`,
   `completedTensor.inr_spaComap_preimage_rationalSubset`,
   `completedTensor.inl_preimage_inter_inr_preimage_rationalSubset`, and their `spaRationalFamily`
   counterparts): `p_B⁻¹(U)`, `p_C⁻¹(V)` and `p_B⁻¹(U) ∩ p_C⁻¹(V)` belong to `spaRationalFamily`,
   with explicit presentation `TauCeti.Huber.CompletedTensor.interPresentation`.
2. **Comparison of completed rational-localisation pairs** (`completedTensor.rationalRingEquiv`,
   `completedTensor.isHomeomorph_rationalRingEquiv`, `completedTensor.map_plus_rationalRingEquiv`,
   `completedTensor.rationalRingEquiv_toCompletion_tmul`): along `O(W) → O(U)` and `O(W) → O(V)`,
   for any presentation `d` of `p_B⁻¹(U) ∩ p_C⁻¹(V)` on `D`, `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)`
   topologically and on rings of integral elements, sending `ρ_B(b) ⊗ₜ ρ_C(c)` to `ρ_D(b ⊗ₜ c)`.
3. **Homeomorphism and rational-subset bijection on `Spa`**
   (`completedTensor.rationalSpaHomeomorph`, `completedTensor.rationalSpaHomeomorph_val`,
   `completedTensor.bijOn_preimage_rationalSpaHomeomorph_spaRationalFamily`):
   `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`, bijecting rational subsets of
   `Spa(D, D⁺)` inside `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.rationalRingEquiv`: topological ring equivalence
  `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)`.
* `TauCeti.Huber.Pair.completedTensor.rationalSpaHomeomorph`: induced homeomorphism
  `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.inl_preimage_inter_inr_preimage_rationalSubset` and
  `inl_preimage_inter_inr_preimage_mem_spaRationalFamily`: rational intersection formula and
  membership in `spaRationalFamily` on `Spa((B, B⁺) ⊗̂_A (C, C⁺))`.
* `TauCeti.Huber.Pair.completedTensor.isHomeomorph_rationalRingEquiv`,
  `map_plus_rationalRingEquiv`, and `rationalRingEquiv_toCompletion_tmul`: topological, plus-ring,
  and pure-tensor compatibility of `rationalRingEquiv`.
* `TauCeti.Huber.Pair.completedTensor.rationalSpaHomeomorph_val` and
  `bijOn_preimage_rationalSpaHomeomorph_spaRationalFamily`: valuation pullback formula and
  rational-subset bijection for `rationalSpaHomeomorph`.

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
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] (UB : Pair B) (UC : Pair C)

open Classical in
/-- Preimage of a rational subset `R(T/s) ⊆ Spa(B, B⁺)` under the left projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_spaComap_preimage_rationalSubset (T : Finset B) (s : B) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C s) := by
  simpa only [completedTensor.toRingHom_inl] using
    (completedTensor.inl A UB UC).spaComap_preimage_rationalSubset T s

open Classical in
/-- Preimage of a rational subset `R(T'/s') ⊆ Spa(C, C⁺)` under the right projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inr_spaComap_preimage_rationalSubset (T' : Finset C) (s' : C) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T'.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C s') := by
  simpa only [completedTensor.toRingHom_inr] using
    (completedTensor.inr A UB UC).spaComap_preimage_rationalSubset T' s'

open Classical in
/-- Intersection of the preimages of `R(T/s) ⊆ Spa(B, B⁺)` and `R(T'/s') ⊆ Spa(C, C⁺)` inside
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_rationalSubset
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
theorem completedTensor.inl_spaComap_preimage_mem_spaRationalFamily
    {U : Set (spa UB.plus)} (hU : U ∈ spaRationalFamily UB.plus) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' U ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by
      simpa only [completedTensor.toRingHom_inl] using
        (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage of a member of `spaRationalFamily UC.plus` along `(inr A UB UC).spaComap` belongs to
`spaRationalFamily` of the completed tensor pair (Wedhorn, Lemma 7.46(3)). -/
theorem completedTensor.inr_spaComap_preimage_mem_spaRationalFamily
    {V : Set (spa UC.plus)} (hV : V ∈ spaRationalFamily UC.plus) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' V ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by
      simpa only [completedTensor.toRingHom_inr] using
        (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

/-- Intersection of the preimages of two rational subsets with open numerator ideals belongs to
`spaRationalFamily` of the completed tensor pair. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_mem_spaRationalFamily
    {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus T' s') ∈
      spaRationalFamily (UB.completedTensor A UC).plus := by
  classical
  exact mem_spaRationalFamily_iff.mpr ⟨_, _, CompletedTensor.isOpen_span_inl_mul_inr hT hT',
    completedTensor.inl_preimage_inter_inr_preimage_rationalSubset UB UC T s T' s'⟩

/-- Degenerate case `U = Spa(B, B⁺)` (`T = {1}`, `s = 1`): intersecting with `p_B⁻¹(R({1}/1))`
leaves `p_C⁻¹(V)` unchanged. -/
theorem completedTensor.inl_preimage_singleton_one_inter (V : Set (spa UC.plus)) :
    (completedTensor.inl A UB UC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset UB.plus {1} 1) ∩
      (completedTensor.inr A UB UC).spaComap ⁻¹' V =
      (completedTensor.inr A UB UC).spaComap ⁻¹' V := by
  rw [rationalSubset_singleton_one, Subtype.coe_preimage_self, Set.preimage_univ, Set.univ_inter]

/-- Degenerate case `s = 0`: `p_B⁻¹(R(T/0)) ∩ p_C⁻¹(R(T'/s'))` is empty. -/
theorem completedTensor.inl_preimage_zero_inter_inr_preimage
    (T : Finset B) (T' : Finset C) (s' : C) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T 0) ∩
      (completedTensor.inr A UB UC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset UC.plus T' s') = ∅ := by
  ext x; simp

end Preimage

open UniformSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withLocPres " P:term:max p:term:max " in " t:term : term =>
  `(letI := locUniformSpace $P ($p).num ($p).den _ ($p).hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace $P ($p).num ($p).den _ ($p).hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace $P ($p).num ($p).den _ ($p).hasDenominatorPower
    letI := isHuberRing_completion_locTopology $P ($p).num ($p).den _ ($p).hasDenominatorPower
    $t)

open UniformSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withFourPres " PA:term:max a:term:max PB:term:max b:term:max
    PC:term:max c:term:max PD:term:max d:term:max " in " t:term : term =>
  `(withLocPres $PA $a in withLocPres $PB $b in withLocPres $PC $c in
    letI := locUniformSpace $PD ($d).num ($d).den _ ($d).hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace $PD ($d).num ($d).den _ ($d).hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace $PD ($d).num ($d).den _ ($d).hasDenominatorPower
    $t)

open UniformSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withRationalCtx "
    PA:term:max UA:term:max hPA:term:max a:term:max
    PB:term:max UB:term:max hPB:term:max b:term:max
    PC:term:max UC:term:max hPC:term:max c:term:max
    PD:term:max d:term:max f:term:max g:term:max
    hf_alg:term:max hg_alg:term:max hf:term:max hg:term:max " in " t:term : term =>
  `(withFourPres $PA $a $PB $b $PC $c $PD $d in
    haveI : IsAdicHom ($f).toRingHom := $hf_alg ▸ inferInstance
    haveI : IsAdicHom ($g).toRingHom := $hg_alg ▸ inferInstance
    let f₀ := pairHomOfSpaComapImageSubset $PA $UA $hPA ($a).num ($a).den _
      ($a).hasDenominatorPower $PB $UB $hPB ($b).num ($b).den _ ($b).hasDenominatorPower $f $hf
    let g₀ := pairHomOfSpaComapImageSubset $PA $UA $hPA ($a).num ($a).den _
      ($a).hasDenominatorPower $PC $UC $hPC ($c).num ($c).den _ ($c).hasDenominatorPower $g $hg
    letI := f₀.toRingHom.toAlgebra
    letI := g₀.toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away ($a).den))
        (Completion (Localization.Away ($b).den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset $PA $UA $hPA ($a).num ($a).den _
        ($a).hasDenominatorPower $PB $UB $hPB ($b).num ($b).den _ ($b).hasDenominatorPower $f $hf
    haveI : IsAdicHom (algebraMap (Completion (Localization.Away ($a).den))
        (Completion (Localization.Away ($c).den))) :=
      isAdicHom_pairHomOfSpaComapImageSubset $PA $UA $hPA ($a).num ($a).den _
        ($a).hasDenominatorPower $PC $UC $hPC ($c).num ($c).den _ ($c).hasDenominatorPower $g $hg
    $t)

open UniformSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition in
open scoped Pointwise in
local macro "withInterLoc " A:term:max B:term:max C:term:max
    PB:term:max b:term:max hb:term:max PC:term:max c:term:max hc:term:max PD:term:max
    num₀:ident den₀:ident hden₀:ident " in " t:term : term =>
  `(letI := ((toCompletionLoc $PB ($b).num ($b).den _ ($b).hasDenominatorPower).comp
      (algebraMap $A $B)).toAlgebra
    letI := ((toCompletionLoc $PC ($c).num ($c).den _ ($c).hasDenominatorPower).comp
      (algebraMap $A $C)).toAlgebra
    haveI : IsAdicHom (algebraMap $A (Completion (Localization.Away ($b).den))) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc $PB ($b).num ($b).den _ ($b).hasDenominatorPower)
        (inferInstanceAs (IsAdicHom (algebraMap $A $B)))
    haveI : IsAdicHom (algebraMap $A (Completion (Localization.Away ($c).den))) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc $PC ($c).num ($c).den _ ($c).hasDenominatorPower)
        (inferInstanceAs (IsAdicHom (algebraMap $A $C)))
    letI := Classical.decEq (CompletedTensor $A $B $C)
    let $num₀ : Finset (CompletedTensor $A $B $C) :=
      insert (CompletedTensor.inl $A $B $C ($b).den)
          (($b).num.image (CompletedTensor.inl $A $B $C)) *
        insert (CompletedTensor.inr $A $B $C ($c).den)
          (($c).num.image (CompletedTensor.inr $A $B $C))
    let $den₀ : CompletedTensor $A $B $C :=
      CompletedTensor.inl $A $B $C ($b).den * CompletedTensor.inr $A $B $C ($c).den
    let $hden₀ := CompletedTensor.hasDenominatorPower_inl_mul_inr $PD
      (s := ($b).den) (s' := ($c).den) $hb $hc (Localization.Away $den₀)
    letI := locUniformSpace $PD $num₀ $den₀ _ $hden₀
    letI := isUniformAddGroup_locUniformSpace $PD $num₀ $den₀ _ $hden₀
    letI := isTopologicalRing_locUniformSpace $PD $num₀ $den₀ _ $hden₀
    letI := isHuberRing_completion_locTopology $PD $num₀ $den₀ _ $hden₀
    $t)

open TauCeti.Huber.PairOfDefinition in
local macro "locPairPres " P:term:max U:term:max hP:term:max p:term:max : term =>
  `(rationalLocalizationPair $P $U $hP ($p).num ($p).den _ ($p).hasDenominatorPower)

open TauCeti.Huber.Pair TauCeti.ValuationSpectrum in
local macro "interPreimage " A:term:max UB:term:max UC:term:max b:term:max c:term:max : term =>
  `((completedTensor.inl $A $UB $UC).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset ($UB).plus ($b).num ($b).den) ∩
    (completedTensor.inr $A $UB $UC).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset ($UC).plus ($c).num ($c).den))

section RationalEquiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
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
      Set (spa (UB.completedTensor A UC).plus)) = interPreimage A UB UC b c)

include hb hc hd in
/-- **Topological ring isomorphism `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(d)`** for presentations `a`, `b`,
`c` of `W ⊆ Spa(A, A⁺)`, `U ⊆ Spa(B, B⁺)`, `V ⊆ Spa(C, C⁺)` with `Spa(f)(U) ⊆ W`, `Spa(g)(V) ⊆ W`,
and any presentation `d` on `D = B ⊗̂_A C` representing `p_B⁻¹(U) ∩ p_C⁻¹(V)`. -/
noncomputable def completedTensor.rationalRingEquiv :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    CompletedTensor (Completion (Localization.Away a.den))
      (Completion (Localization.Away b.den))
      (Completion (Localization.Away c.den)) ≃+* Completion (Localization.Away d.den) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
  withInterLoc A B C PB b hb PC c hc PD num₀ den₀ hden₀ in
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
      (rationalSubset_eq_of_spaBasicOpen_eq <| SetLike.ext fun v ↦ by
        simpa only [mem_spaBasicOpen, Set.mem_preimage] using Set.ext_iff.mp
          ((completedTensor.inl_preimage_inter_inr_preimage_rationalSubset UB UC b.num b.den
            c.num c.den).symm.trans hd.symm) v))

/-- `completedTensor.rationalRingEquiv` is continuous. -/
theorem completedTensor.continuous_rationalRingEquiv :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    Continuous (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
  withInterLoc A B C PB b hb PC c hc PD num₀ den₀ hden₀ in by
    dsimp only [completedTensor.rationalRingEquiv]
    rw [RingEquiv.coe_trans, RingEquiv.coe_trans]
    exact (continuous_presentationRingEquivOfEq PD (UB.completedTensor A UC).plus _
        num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _).comp
      ((continuous_completionLocEquiv PB b.num b.den _ b.hasDenominatorPower
          PC c.num c.den _ c.hasDenominatorPower PD _ hden₀).comp
        (continuous_completionLocBaseEquiv PA a.num a.den _ a.hasDenominatorPower _ _ _ _ _ _))

/-- The inverse of `completedTensor.rationalRingEquiv` is continuous. -/
theorem completedTensor.continuous_rationalRingEquiv_symm :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    Continuous (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd).symm :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
  withInterLoc A B C PB b hb PC c hc PD num₀ den₀ hden₀ in by
    dsimp only [completedTensor.rationalRingEquiv]
    rw [RingEquiv.symm_trans, RingEquiv.symm_trans, RingEquiv.coe_trans, RingEquiv.coe_trans]
    exact ((continuous_completionLocBaseEquiv_symm PA a.num a.den _ a.hasDenominatorPower _ _ _ _ _
        _).comp
      (continuous_completionLocEquiv_symm PB b.num b.den _ b.hasDenominatorPower
        PC c.num c.den _ c.hasDenominatorPower PD _ hden₀)).comp
      (continuous_presentationRingEquivOfEq_symm PD (UB.completedTensor A UC).plus _
        num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _)

/-- `completedTensor.rationalRingEquiv` is a homeomorphism. -/
theorem completedTensor.isHomeomorph_rationalRingEquiv :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    IsHomeomorph (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
      PD d f g hf_alg hg_alg hf hg hd) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
      hf_alg hg_alg hf hg hd).toEquiv.isHomeomorph_iff.mpr
      ⟨completedTensor.continuous_rationalRingEquiv ..,
        completedTensor.continuous_rationalRingEquiv_symm PA UA hPA a PB UB hPB b hb PC UC hPC c hc
          PD d f g hf_alg hg_alg hf hg hd⟩

include hPD in
/-- `completedTensor.rationalRingEquiv` carries the completed tensor plus ring of `O(U)` and
`O(V)` over `O(W)` onto `completedPlusSubring` of `d`. -/
theorem completedTensor.map_plus_rationalRingEquiv :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    (((locPairPres PB UB hPB b).completedTensor (Completion (Localization.Away a.den))
        (locPairPres PC UC hPC c)).plus.map
      (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd : _ →+* _)) =
      completedPlusSubring PD (UB.completedTensor A UC).plus d.num d.den _ d.hasDenominatorPower :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
  withInterLoc A B C PB b hb PC c hc PD num₀ den₀ hden₀ in by
    dsimp only [completedTensor.rationalRingEquiv]
    rw [← RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_trans', RingEquiv.toRingHom_trans',
      ← Subring.map_map, ← Subring.map_map,
      completedTensor.map_plus_completionLocBaseEquiv PA a.num a.den _ a.hasDenominatorPower,
      completedTensor.map_plus_completionLocEquiv PB UB b.num b.den _ b.hasDenominatorPower
        PC UC c.num c.den _ c.hasDenominatorPower PD _ hden₀ hPB hPC hPD,
      rationalLocalizationPair_plus]
    exact map_completedPlusSubring_presentationRingEquivOfEq PD (UB.completedTensor A UC).plus
      (fun j _ ↦ hPD j.2) (UB.completedTensor A UC).isRingOfIntegralElements.isPowerBounded_of_mem
      num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _

/-- **Pure-tensor coefficient formula for `completedTensor.rationalRingEquiv`**:
`e(ρ_B(x) ⊗ₜ ρ_C(y)) = ρ_D(x ⊗ₜ y)`. -/
theorem completedTensor.rationalRingEquiv_toCompletion_tmul (x : B) (y : C) :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd
        (CompletedTensor.toCompletion (Completion (Localization.Away a.den))
          (Completion (Localization.Away b.den)) (Completion (Localization.Away c.den))
          (toCompletionLoc PB b.num b.den _ b.hasDenominatorPower x ⊗ₜ
            toCompletionLoc PC c.num c.den _ c.hasDenominatorPower y)) =
      toCompletionLoc PD d.num d.den _ d.hasDenominatorPower
        (CompletedTensor.toCompletion A B C (x ⊗ₜ y)) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
  withInterLoc A B C PB b hb PC c hc PD num₀ den₀ hden₀ in by
    dsimp only [completedTensor.rationalRingEquiv]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, completionLocBaseEquiv_toCompletion_tmul,
      completionLocEquiv_toCompletion_tmul]
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using
      RingHom.congr_fun
        (presentationRingEquivOfEq_coe_comp_toCompletionLoc PD (UB.completedTensor A UC).plus _
          num₀ den₀ _ hden₀ d.num d.den _ d.hasDenominatorPower _) _

include hb hc hPD hd in
/-- **Homeomorphism `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`** pulling valuations back
along `e⁻¹ ∘ ρ_D` (Huber 1994, Lemma 1.5(ii); Wedhorn, Proposition 8.2(2)). -/
noncomputable def completedTensor.rationalSpaHomeomorph :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    spa ((locPairPres PB UB hPB b).completedTensor (Completion (Localization.Away a.den))
        (locPairPres PC UC hPC c)).plus ≃ₜ ↥(interPreimage A UB UC b c) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    ((spaHomeomorphOfRingEquiv
        (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
          hf_alg hg_alg hf hg hd)
        (completedTensor.continuous_rationalRingEquiv ..)
        (completedTensor.continuous_rationalRingEquiv_symm ..)
        (completedTensor.map_plus_rationalRingEquiv (hPD := hPD) ..)).trans
      (spaCompletedLocalizationHomeomorph PD (UB.completedTensor A UC).plus hPD d.num d.den _
        d.hasDenominatorPower)).trans
      (Homeomorph.setCongr hd)

/-- `completedTensor.rationalSpaHomeomorph` pulls valuations back along `e.symm ∘ ρ_D`. -/
@[simp] theorem completedTensor.rationalSpaHomeomorph_val :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    ∀ v : spa ((locPairPres PB UB hPB b).completedTensor (Completion (Localization.Away a.den))
        (locPairPres PC UC hPC c)).plus,
      ((completedTensor.rationalSpaHomeomorph PA UA hPA a PB UB hPB b hb PC UC hPC c hc
          PD hPD d f g hf_alg hg_alg hf hg hd v).1 : Spv (CompletedTensor A B C)) =
        ValuationSpectrum.comap
          ((completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc
              PD d f g hf_alg hg_alg hf hg hd).symm.toRingHom.comp
            (toCompletionLoc PD d.num d.den _ d.hasDenominatorPower)) v.1 :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in by
    dsimp only [completedTensor.rationalSpaHomeomorph]
    intro v
    simp only [Homeomorph.trans_apply, Homeomorph.setCongr_apply,
      spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, spaComapLoc_val,
      spaHomeomorphOfRingEquiv_val, ← RingEquiv.toRingHom_eq_coe]
    rw [← Function.comp_apply
        (f := ValuationSpectrum.comap (toCompletionLoc PD d.num d.den _ d.hasDenominatorPower)),
      ← ValuationSpectrum.comap_comp]

include hd_open in
/-- Preimage under `completedTensor.rationalSpaHomeomorph` bijects rational subsets of `Spa(D, D⁺)`
contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily` of `Spa(O(U) ⊗̂_{O(W)} O(V))`. -/
theorem completedTensor.bijOn_preimage_rationalSpaHomeomorph_spaRationalFamily :
    withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in
    Set.BijOn (fun Z : Set (spa (UB.completedTensor A UC).plus) ↦
        completedTensor.rationalSpaHomeomorph PA UA hPA a PB UB hPB b hb PC UC hPC c hc
          PD hPD d f g hf_alg hg_alg hf hg hd ⁻¹' (Subtype.val ⁻¹' Z))
      {Z ∈ spaRationalFamily (UB.completedTensor A UC).plus | Z ⊆ interPreimage A UB UC b c}
      (spaRationalFamily ((locPairPres PB UB hPB b).completedTensor
        (Completion (Localization.Away a.den)) (locPairPres PC UC hPC c)).plus) :=
  withRationalCtx PA UA hPA a PB UB hPB b PC UC hPC c PD d f g hf_alg hg_alg hf hg in by
    have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily
      (completedTensor.rationalRingEquiv PA UA hPA a PB UB hPB b hb PC UC hPC c hc PD d f g
        hf_alg hg_alg hf hg hd)
      (completedTensor.continuous_rationalRingEquiv ..)
      (completedTensor.continuous_rationalRingEquiv_symm ..)
      (completedTensor.map_plus_rationalRingEquiv (hPD := hPD) ..)
    have hbij₂ := bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily
      PD (UB.completedTensor A UC).plus hPD d.num d.den hd_open _ d.hasDenominatorPower
    have hdom : {W ∈ spaRationalFamily (UB.completedTensor A UC).plus |
          W ⊆ Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus d.num d.den} =
        {Z ∈ spaRationalFamily (UB.completedTensor A UC).plus |
          Z ⊆ interPreimage A UB UC b c} := by
      simp only [hd]
    rw [hdom] at hbij₂
    exact (hbij₁.comp hbij₂).congr fun Z _ ↦ by
      ext x; simp [completedTensor.rationalSpaHomeomorph]

end RationalEquiv

end TauCeti.Huber.Pair
