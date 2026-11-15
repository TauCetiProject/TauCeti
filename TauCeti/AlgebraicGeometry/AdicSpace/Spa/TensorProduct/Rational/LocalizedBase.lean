/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Epimorphism

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.RingOfDefinition
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Completed tensor products of rational localisations over a localized base

Let `(A, A⁺)`, `(B, B⁺)`, and `(C, C⁺)` be Huber pairs equipped with adic structure maps `A → B`
and `A → C`, and write `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)`. Suppose `R_A(T_A / s_A) ⊆ Spa(A, A⁺)`,
`U = R_B(T_B / s_B) ⊆ Spa(B, B⁺)`, and `V = R_C(T_C / s_C) ⊆ Spa(C, C⁺)` are rational subsets such
that pullback along `A → B` maps `U` into `R_A(T_A / s_A)` and pullback along `A → C` maps `V` into
`R_A(T_A / s_A)` (note that `A → B` and `A → C` need not carry all of `A⁺` into `B⁺` or `C⁺`).

1. **Adic `A⟨T_A/s_A⟩`-algebra structure (`Pair.ratLocAlgebra`, `Pair.isAdicHom_ratLocAlgebra`).**
   Geometric functoriality of completed rational localisations (`ringHomOfMapsToRationalSubset`)
   equips `B⟨T_B/s_B⟩` and `C⟨T_C/s_C⟩` with canonical adic `A⟨T_A/s_A⟩`-algebra structures
   compatible with `A → B⟨T_B/s_B⟩` and `A → C⟨T_C/s_C⟩`.
2. **Localized-base Huber-pair isomorphism (`localizedBaseRatLocEquiv`,
   `map_localizedBaseRatLocEquiv_plus`).** Combining epimorphic base invariance
   `B⟨T_B/s_B⟩ ⊗̂_A C⟨T_C/s_C⟩ ≃+* B⟨T_B/s_B⟩ ⊗̂_{A⟨T_A/s_A⟩} C⟨T_C/s_C⟩` with the unlocalized-base
   comparison `ratLocEquiv` yields a homeomorphic Huber-pair isomorphism
   `(B⟨T_B/s_B⟩, B_U⁺) ⊗̂_{(A⟨T_A/s_A⟩, A_W⁺)} (C⟨T_C/s_C⟩, C_V⁺) ≃ (D⟨T_D/s_D⟩, D_{U×V}⁺)` for
   any presentation `(T_D, s_D)` of `p_B⁻¹(U) ∩ p_C⁻¹(V)`, inducing a homeomorphism of adic spectra
   with `p_B⁻¹(U) ∩ p_C⁻¹(V)` (`localizedBaseRatLocSpaHomeomorph`) and bijecting rational subsets
   (`bijOn_preimage_localizedBaseRatLocSpaHomeomorph_spaRationalFamily`,
   `bijOn_preimage_localizedBaseRatLocSpaHomeomorph_canonical`).
3. **Single-factor completed base change (`baseChangeRatLocEquiv`,
   `baseChangeRatLocSpaHomeomorph`).**
   For a single Huber pair `(B, B⁺)` over `A`, `(B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺)` is canonically
   homeomorphically isomorphic as a Huber pair to `(B⟨T_B/s_B⟩, B_U⁺)` whenever `R_B(T_B / s_B)`
   cuts out `comap (algebraMap A B) ⁻¹' R_A(T_A / s_A) ∩ Spa(B, B⁺)`.
4. **Degenerate and non-vacuous regimes (`subsingleton_and_spa_eq_empty_of_denom_zero`,
   `nontrivial_and_spa_nonempty_localizedBase_of_discrete`).** When `s_B = 0`, the localized-base
   completed tensor ring is trivial and its adic spectrum is empty; over any nontrivial discrete
   commutative ring `R`, the localized-base completed tensor product of `R × R` with itself over
   `R⟨{1}/1⟩` is nontrivial with nonempty adic spectrum.

## Main definitions and results

* `TauCeti.Huber.ratLocMapAlgebra` and `TauCeti.Huber.Pair.ratLocAlgebra`: the induced adic
  `A⟨T_A/s_A⟩`-algebra structure on `B⟨T_B/s_B⟩`.
* `Pair.completedTensor.localizedBaseRatLocEquiv`,
  `Pair.completedTensor.map_localizedBaseRatLocEquiv_plus`,
  `Pair.completedTensor.localizedBaseRatLocSpaHomeomorph`,
  `Pair.completedTensor.bijOn_preimage_localizedBaseRatLocSpaHomeomorph_spaRationalFamily`:
  Huber-pair isomorphism, `Spa` homeomorphism, and rational-subset bijection over `A⟨T_A/s_A⟩`.
* `Pair.completedTensor.baseChangeRatLocEquiv`,
  `Pair.completedTensor.map_baseChangeRatLocEquiv_plus`,
  `Pair.completedTensor.baseChangeRatLocSpaHomeomorph`:
  single-factor completed base change `(B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺) ≃ (B⟨T_B/s_B⟩, B_U⁺)`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2, Proposition
  1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber

open PairOfDefinition ValuationSpectrum

universe u v w

/-! ### Induced `A⟨T_A/s_A⟩`-algebra structure on `B⟨T_B/s_B⟩` -/

section RatLocMapAlgebra

/-- When `comap (algebraMap A B)` maps `R_B(T_B/s_B)` into `R_A(T_A/s_A)` and `B⁺` consists of
power-bounded elements, `ringHomOfMapsToRationalSubset` equips `B⟨T_B/s_B⟩` with a canonical
`A⟨T_A/s_A⟩`-algebra structure. -/
@[expose, instance_reducible]
noncomputable def ratLocMapAlgebra
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (QA : PairOfDefinition A) (Aplus : Subring A) (T_A : Finset A) (s_A : A)
    (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
    {B : Type*} [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsAdicHom (algebraMap A B)]
    (QB : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T_B : Finset B) (s_B : B)
    (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
    (hmaps : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset Bplus T_B s_B) (rationalSubset Aplus T_A s_A)) :
    Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B) :=
  (ringHomOfMapsToRationalSubset QA Aplus T_A s_A (Localization.Away s_A) hden_A
    QB Bplus hBplus T_B s_B (Localization.Away s_B) hden_B
    (algebraMap A B) (IsAdicHom.continuous inferInstance) hmaps).toAlgebra

section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (QA : PairOfDefinition A) (Aplus : Subring A) (T_A : Finset A) (s_A : A)
  (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
  {B : Type*} [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsAdicHom (algebraMap A B)]
  (QB : PairOfDefinition B) (Bplus : Subring B)
  (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (T_B : Finset B) (s_B : B)
  (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
  (hmaps : Set.MapsTo (comap (algebraMap A B))
    (rationalSubset Bplus T_B s_B) (rationalSubset Aplus T_A s_A))

attribute [local instance 900] ratLocBaseAlgebra

/-- The structure map of `ratLocMapAlgebra` is `ringHomOfMapsToRationalSubset`. -/
theorem algebraMap_ratLocMapAlgebra :
    letI := ratLocMapAlgebra QA Aplus T_A s_A hden_A QB Bplus hBplus T_B s_B hden_B hmaps
    algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B) =
      ringHomOfMapsToRationalSubset QA Aplus T_A s_A (Localization.Away s_A) hden_A
        QB Bplus hBplus T_B s_B (Localization.Away s_B) hden_B
        (algebraMap A B) (IsAdicHom.continuous inferInstance) hmaps :=
  rfl

/-- Composing `A⟨T_A/s_A⟩ → B⟨T_B/s_B⟩` with `A → A⟨T_A/s_A⟩` recovers `ratLocBaseAlgebra`. -/
theorem algebraMap_ratLocMapAlgebra_comp :
    letI := ratLocMapAlgebra QA Aplus T_A s_A hden_A QB Bplus hBplus T_B s_B hden_B hmaps
    (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)).comp
        (algebraMap A (ratLoc QA T_A s_A hden_A)) =
      algebraMap A (ratLoc QB T_B s_B hden_B) := by
  let _ := ratLocMapAlgebra QA Aplus T_A s_A hden_A QB Bplus hBplus T_B s_B hden_B hmaps
  rw [algebraMap_ratLocMapAlgebra, algebraMap_ratLoc QA,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
  rfl

/-- The induced map `A⟨T_A/s_A⟩ → B⟨T_B/s_B⟩` is adic whenever `A → B` is adic. -/
theorem isAdicHom_ratLocMapAlgebra :
    letI := ratLocMapAlgebra QA Aplus T_A s_A hden_A QB Bplus hBplus T_B s_B hden_B hmaps
    IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)) :=
  isAdicHom_ringHomOfMapsToRationalSubset QA Aplus T_A s_A (Localization.Away s_A) hden_A
    QB Bplus hBplus T_B s_B (Localization.Away s_B) hden_B
    (algebraMap A B) (IsAdicHom.continuous inferInstance) inferInstance hmaps

end

/-- Bundled Huber-pair form of `ratLocMapAlgebra`: when `comap (algebraMap A B)` maps
`R_B(T_B/s_B)` into `R_A(T_A/s_A)`, `B⟨T_B/s_B⟩` is canonically an adic `A⟨T_A/s_A⟩`-algebra. -/
@[expose, instance_reducible]
noncomputable def Pair.ratLocAlgebra
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    (PA : Pair A) (QA : PairOfDefinition A) (T_A : Finset A) (s_A : A)
    (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
    {B : Type*} [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsHuberRing B] [IsAdicHom (algebraMap A B)]
    (PB : Pair B) (QB : PairOfDefinition B) (T_B : Finset B) (s_B : B)
    (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
    (hmaps : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset PB.plus T_B s_B) (rationalSubset PA.plus T_A s_A)) :
    Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B) :=
  ratLocMapAlgebra QA PA.plus T_A s_A hden_A QB PB.plus
    PB.isRingOfIntegralElements.isPowerBounded_of_mem T_B s_B hden_B hmaps

section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (PA : Pair A) (QA : PairOfDefinition A) (T_A : Finset A) (s_A : A)
  (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
  {B : Type*} [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] [IsAdicHom (algebraMap A B)]
  (PB : Pair B) (QB : PairOfDefinition B) (T_B : Finset B) (s_B : B)
  (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
  (hmaps : Set.MapsTo (comap (algebraMap A B))
    (rationalSubset PB.plus T_B s_B) (rationalSubset PA.plus T_A s_A))

attribute [local instance 900] ratLocBaseAlgebra

/-- Composing `Pair.ratLocAlgebra`'s structure map with `A → A⟨T_A/s_A⟩` recovers
`ratLocBaseAlgebra`. -/
theorem Pair.algebraMap_ratLocAlgebra_comp :
    letI := Pair.ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B s_B hden_B hmaps
    (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)).comp
        (algebraMap A (ratLoc QA T_A s_A hden_A)) =
      algebraMap A (ratLoc QB T_B s_B hden_B) :=
  algebraMap_ratLocMapAlgebra_comp QA PA.plus T_A s_A hden_A QB PB.plus
    PB.isRingOfIntegralElements.isPowerBounded_of_mem T_B s_B hden_B hmaps

/-- `Pair.ratLocAlgebra` makes `A⟨T_A/s_A⟩ → B⟨T_B/s_B⟩` an adic ring homomorphism. -/
theorem Pair.isAdicHom_ratLocAlgebra :
    letI := Pair.ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B s_B hden_B hmaps
    IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)) :=
  isAdicHom_ratLocMapAlgebra QA PA.plus T_A s_A hden_A QB PB.plus
    PB.isRingOfIntegralElements.isPowerBounded_of_mem T_B s_B hden_B hmaps

end

end RatLocMapAlgebra

/-! ### Completed tensor products over a localized base `A⟨T_A/s_A⟩` -/

namespace Pair.completedTensor

private theorem comap_comap_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (v : Spv T) :
    comap f (comap g v) = comap (g.comp f) v :=
  (congr_fun (comap_comp f g) v).symm

section LocalizedBase

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

private theorem ratLoc_epimorphismBase
    (QA : PairOfDefinition A) (T_A : Finset A) (s_A : A)
    (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
    {E : Type*} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    (g h : ratLoc QA T_A s_A hden_A →+* E) (hg : Continuous g) (hh : Continuous h)
    (heq : g.comp (algebraMap A (ratLoc QA T_A s_A hden_A)) =
      h.comp (algebraMap A (ratLoc QA T_A s_A hden_A))) :
    g = h := by
  rw [algebraMap_ratLoc QA] at heq
  exact completion_locTopology_ringHom_ext_of_continuous QA T_A s_A (Localization.Away s_A)
    hden_A g h hg hh heq

variable
  (QA : PairOfDefinition A)
  (T_A : Finset A) (s_A : A) (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
  (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (T_B : Finset B) (s_B : B) (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
  [Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)]
  [IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B))]
  (hcomp_B : (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)).comp
      (algebraMap A (ratLoc QA T_A s_A hden_A)) = algebraMap A (ratLoc QB T_B s_B hden_B))
  (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
  (T_C : Finset C) (s_C : C) (hden_C : QC.HasDenominatorPower T_C s_C (Localization.Away s_C))
  [Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C)]
  [IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C))]
  (hcomp_C : (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C)).comp
      (algebraMap A (ratLoc QA T_A s_A hden_A)) = algebraMap A (ratLoc QC T_C s_C hden_C))
  (QD : PairOfDefinition (CompletedTensor A B C))
  (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus)
  (T_D : Finset (CompletedTensor A B C)) (s_D : CompletedTensor A B C)
  (hden_D : QD.HasDenominatorPower T_D s_D (Localization.Away s_D))
  (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
      Set (spa (PB.completedTensor A PC).plus)) =
    (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
      (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C))

/-- **Topological ring isomorphism
`B⟨T_B/s_B⟩ ⊗̂_{A⟨T_A/s_A⟩} C⟨T_C/s_C⟩ ≃+* D⟨T_D/s_D⟩`** when `B⟨T_B/s_B⟩` and `C⟨T_C/s_C⟩` are adic
`A⟨T_A/s_A⟩`-algebras compatible with `A` and `(T_D, s_D)` cuts out `p_B⁻¹(U) ∩ p_C⁻¹(V)`. -/
noncomputable def localizedBaseRatLocEquiv :
    CompletedTensor (ratLoc QA T_A s_A hden_A)
      (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C) ≃+*
      ratLoc QD T_D s_D hden_D :=
  (CompletedTensor.epimorphismBaseEquiv
    (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)
    (algebraMap A (ratLoc QA T_A s_A hden_A)) hcomp_B hcomp_C
    (ratLoc_epimorphismBase QA T_A s_A hden_A)).symm.trans
    (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV)

/-- `localizedBaseRatLocEquiv` is continuous. -/
@[fun_prop]
theorem continuous_localizedBaseRatLocEquiv :
    Continuous (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV) :=
  (continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).comp
    (CompletedTensor.continuous_epimorphismBaseEquiv_symm
      (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)
      (algebraMap A (ratLoc QA T_A s_A hden_A)) hcomp_B hcomp_C
      (ratLoc_epimorphismBase QA T_A s_A hden_A))

/-- `(localizedBaseRatLocEquiv …).symm` is continuous. -/
@[fun_prop]
theorem continuous_localizedBaseRatLocEquiv_symm :
    Continuous (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm :=
  (CompletedTensor.continuous_epimorphismBaseEquiv
    (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)
    (algebraMap A (ratLoc QA T_A s_A hden_A)) hcomp_B hcomp_C
    (ratLoc_epimorphismBase QA T_A s_A hden_A)).comp
    (continuous_ratLocEquiv_symm QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV)

/-- `localizedBaseRatLocEquiv` is a homeomorphism. -/
theorem isHomeomorph_localizedBaseRatLocEquiv :
    IsHomeomorph (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV) :=
  (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
    QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV,
     continuous_localizedBaseRatLocEquiv_symm QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV⟩

/-- `localizedBaseRatLocEquiv` sends `inl (algebraMap B _ b)` to `algebraMap D _ (inl b)`. -/
@[simp]
theorem localizedBaseRatLocEquiv_inl_algebraMap (b : B) :
    localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.inl (ratLoc QA T_A s_A hden_A) _ _
          (algebraMap B (ratLoc QB T_B s_B hden_B) b)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inl A B C b) := by
  simp [localizedBaseRatLocEquiv]

/-- `localizedBaseRatLocEquiv` sends `inr (algebraMap C _ c)` to `algebraMap D _ (inr c)`. -/
@[simp]
theorem localizedBaseRatLocEquiv_inr_algebraMap (c : C) :
    localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.inr (ratLoc QA T_A s_A hden_A) _ _
          (algebraMap C (ratLoc QC T_C s_C hden_C) c)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inr A B C c) := by
  simp [localizedBaseRatLocEquiv]

/-- `localizedBaseRatLocEquiv` sends pure tensors of images of `b : B` and `c : C` to the image of
`b ⊗ₜ[A] c`. -/
theorem localizedBaseRatLocEquiv_tmul_algebraMap (b : B) (c : C) :
    localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.toCompletion (ratLoc QA T_A s_A hden_A) _ _
          (algebraMap B (ratLoc QB T_B s_B hden_B) b ⊗ₜ[ratLoc QA T_A s_A hden_A]
            algebraMap C (ratLoc QC T_C s_C hden_C) c)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c)) := by
  simp

/-- `(localizedBaseRatLocEquiv …).symm` sends `algebraMap D _ (inl b)` to
`inl (algebraMap B _ b)`. -/
@[simp]
theorem localizedBaseRatLocEquiv_symm_algebraMap_inl (b : B) :
    (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
          (CompletedTensor.inl A B C b)) =
      CompletedTensor.inl (ratLoc QA T_A s_A hden_A) _ _
        (algebraMap B (ratLoc QB T_B s_B hden_B) b) := by
  apply (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
    QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).injective
  simp

/-- `(localizedBaseRatLocEquiv …).symm` sends `algebraMap D _ (inr c)` to
`inr (algebraMap C _ c)`. -/
@[simp]
theorem localizedBaseRatLocEquiv_symm_algebraMap_inr (c : C) :
    (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
          (CompletedTensor.inr A B C c)) =
      CompletedTensor.inr (ratLoc QA T_A s_A hden_A) _ _
        (algebraMap C (ratLoc QC T_C s_C hden_C) c) := by
  apply (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
    QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).injective
  simp

/-- **`localizedBaseRatLocEquiv` preserves membership in the rings of integral elements in both
directions.** -/
@[simp]
theorem localizedBaseRatLocEquiv_mem_plus_iff
    (x : CompletedTensor (ratLoc QA T_A s_A hden_A)
      (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)) :
    localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV x ∈
        (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
          (Localization.Away s_D) hden_D).plus ↔
      x ∈ ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus := by
  simp only [localizedBaseRatLocEquiv, RingEquiv.trans_apply, ratLocEquiv_mem_plus_iff]
  have h := epimorphismBaseEquiv_mem_plus_iff
    (algebraMap A (ratLoc QA T_A s_A hden_A)) hcomp_B hcomp_C
    (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B)
    (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)
    (ratLoc_epimorphismBase QA T_A s_A hden_A)
    ((CompletedTensor.epimorphismBaseEquiv
      (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)
      (algebraMap A (ratLoc QA T_A s_A hden_A)) hcomp_B hcomp_C
      (ratLoc_epimorphismBase QA T_A s_A hden_A)).symm x)
  simpa using h.symm

/-- **`localizedBaseRatLocEquiv` carries the completed tensor plus ring over `A⟨T_A/s_A⟩` onto
`D_{U×V}⁺`.** -/
theorem map_localizedBaseRatLocEquiv_plus :
    ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus.map
        (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
          QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV : _ →+* _) =
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
        (Localization.Away s_D) hden_D).plus := by
  ext y
  rw [Subring.mem_map_equiv]
  have h := (localizedBaseRatLocEquiv_mem_plus_iff QA T_A s_A hden_A QB PB hQB T_B s_B hden_B
    hcomp_B QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV
    ((localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm y)).symm
  simpa using h

/-- **Homeomorphism identifying
`Spa((B⟨T_B/s_B⟩, B_U⁺) ⊗̂_{(A⟨T_A/s_A⟩, A_W⁺)} (C⟨T_C/s_C⟩, C_V⁺))` with
`p_B⁻¹(U) ∩ p_C⁻¹(V) ⊆ Spa((B, B⁺) ⊗̂_A (C, C⁺))`.** -/
noncomputable def localizedBaseRatLocSpaHomeomorph :
    spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus ≃ₜ
      ((inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C) :
        Set (spa (PB.completedTensor A PC).plus)) :=
  (((spaHomeomorphOfRingEquiv
      (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
      (continuous_localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
      (continuous_localizedBaseRatLocEquiv_symm QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
      (map_localizedBaseRatLocEquiv_plus QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)).symm).trans
    (spaRationalLocalizationPairHomeomorph QD (PB.completedTensor A PC) hQD T_D s_D
      (Localization.Away s_D) hden_D)).trans
    (Homeomorph.setCongr hUV)

/-- Explicit valuation-level formula for `localizedBaseRatLocSpaHomeomorph`. -/
theorem localizedBaseRatLocSpaHomeomorph_coe_val
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    ((localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
        QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV w :
        spa (PB.completedTensor A PC).plus)).1 =
      comap (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))
        (comap (RingEquiv.toRingHom
          (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
            QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm) w.1) := by
  simp only [localizedBaseRatLocSpaHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    spaRationalLocalizationPairHomeomorph_coe_val, spaHomeomorphOfRingEquiv_symm_val,
    algebraMap_ratLoc QD]
  rfl

/-- **`localizedBaseRatLocSpaHomeomorph` commutes with the first projection to `Spa(B, B⁺)`.** -/
theorem spaComap_inl_localizedBaseRatLocSpaHomeomorph
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    (inl A PB PC).spaComap
        (localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
          QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV w :
          spa (PB.completedTensor A PC).plus) =
      (spaRationalLocalizationPairHomeomorph QB PB hQB T_B s_B (Localization.Away s_B) hden_B
        ((inl (ratLoc QA T_A s_A hden_A) _ _).spaComap w) : spa PB.plus) := by
  apply Subtype.ext
  rw [Hom.spaComap_val, toRingHom_inl, localizedBaseRatLocSpaHomeomorph_coe_val,
    spaRationalLocalizationPairHomeomorph_coe_val, Hom.spaComap_val, toRingHom_inl,
    ← algebraMap_ratLoc QB, comap_comap_apply, comap_comap_apply, comap_comap_apply,
    ← RingHom.comp_assoc]
  have hhom :
      (RingEquiv.toRingHom
          (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
            QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm |>.comp
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))).comp
        (CompletedTensor.inl A B C) =
      (CompletedTensor.inl (ratLoc QA T_A s_A hden_A)
        (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)).comp
        (algebraMap B (ratLoc QB T_B s_B hden_B)) := by
    ext b
    simp
  rw [hhom]

/-- **`localizedBaseRatLocSpaHomeomorph` commutes with the second projection to `Spa(C, C⁺)`.** -/
theorem spaComap_inr_localizedBaseRatLocSpaHomeomorph
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    (inr A PB PC).spaComap
        (localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
          QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV w :
          spa (PB.completedTensor A PC).plus) =
      (spaRationalLocalizationPairHomeomorph QC PC hQC T_C s_C (Localization.Away s_C) hden_C
        ((inr (ratLoc QA T_A s_A hden_A) _ _).spaComap w) : spa PC.plus) := by
  apply Subtype.ext
  rw [Hom.spaComap_val, toRingHom_inr, localizedBaseRatLocSpaHomeomorph_coe_val,
    spaRationalLocalizationPairHomeomorph_coe_val, Hom.spaComap_val, toRingHom_inr,
    ← algebraMap_ratLoc QC, comap_comap_apply, comap_comap_apply, comap_comap_apply,
    ← RingHom.comp_assoc]
  have hhom :
      (RingEquiv.toRingHom
          (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
            QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV).symm |>.comp
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))).comp
        (CompletedTensor.inr A B C) =
      (CompletedTensor.inr (ratLoc QA T_A s_A hden_A)
        (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)).comp
        (algebraMap C (ratLoc QC T_C s_C hden_C)) := by
    ext c
    simp
  rw [hhom]

/-- **Pullback along `localizedBaseRatLocSpaHomeomorph` bijects rational subsets of `Spa(D, D⁺)`
contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily` of the localized-base completed tensor
spectrum.** -/
theorem bijOn_preimage_localizedBaseRatLocSpaHomeomorph_spaRationalFamily
    (hTD : IsOpen (Ideal.span (T_D : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C))) :
    Set.BijOn (fun W : Set (spa (PB.completedTensor A PC).plus) ↦
        localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
          QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)}
      (spaRationalFamily ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) := by
  have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_symm_spaRationalFamily
    (localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
    (continuous_localizedBaseRatLocEquiv QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
    (continuous_localizedBaseRatLocEquiv_symm QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
    (map_localizedBaseRatLocEquiv_plus QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
      QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV)
  have hbij₂ := bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily
    QD (PB.completedTensor A PC) hQD T_D s_D hTD (Localization.Away s_D) hden_D
  have hdom :
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)} =
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D} := by
    rw [hUV]
  exact hdom ▸ (hbij₁.comp hbij₂).congr fun W _ ↦ by
    ext w
    simp [localizedBaseRatLocSpaHomeomorph]

include hcomp_B hcomp_C QD hQD T_D s_D hden_D hUV in
/-- The localized-base completed tensor adic spectrum is nonempty if and only if
`p_B⁻¹(U) ∩ p_C⁻¹(V)` is nonempty. -/
theorem localizedBaseRatLoc_spa_nonempty_iff :
    (spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus).Nonempty
      ↔
      ((inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)).Nonempty := by
  let h := localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
    QC PC hQC T_C s_C hden_C hcomp_C QD hQD T_D s_D hden_D hUV
  simpa only [Set.nonempty_coe_sort] using h.toEquiv.nonempty_congr

end LocalizedBase

section LocalizedBaseCanonical

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

open scoped Pointwise in
/-- **Specialization of `bijOn_preimage_localizedBaseRatLocSpaHomeomorph_spaRationalFamily` to the
canonical presentation `T_D = ({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C))`,
`s_D = inl(s_B) · inr(s_C)`.** -/
theorem bijOn_preimage_localizedBaseRatLocSpaHomeomorph_canonical
    [inst : DecidableEq (CompletedTensor A B C)]
    (QA : PairOfDefinition A)
    (T_A : Finset A) (s_A : A) (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
    (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
    (T_B : Finset B) (s_B : B) (hTB : IsOpen (Ideal.span (T_B : Set B) : Set B))
    (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
    [Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)]
    [IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B))]
    (hcomp_B : (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QB T_B s_B hden_B)).comp
        (algebraMap A (ratLoc QA T_A s_A hden_A)) = algebraMap A (ratLoc QB T_B s_B hden_B))
    (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
    (T_C : Finset C) (s_C : C) (hTC : IsOpen (Ideal.span (T_C : Set C) : Set C))
    (hden_C : QC.HasDenominatorPower T_C s_C (Localization.Away s_C))
    [Algebra (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C)]
    [IsAdicHom (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C))]
    (hcomp_C : (algebraMap (ratLoc QA T_A s_A hden_A) (ratLoc QC T_C s_C hden_C)).comp
        (algebraMap A (ratLoc QA T_A s_A hden_A)) = algebraMap A (ratLoc QC T_C s_C hden_C))
    (QD : PairOfDefinition (CompletedTensor A B C))
    (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus) :
    Set.BijOn (fun W : Set (spa (PB.completedTensor A PC).plus) ↦
        localizedBaseRatLocSpaHomeomorph QA T_A s_A hden_A QB PB hQB T_B s_B hden_B hcomp_B
          QC PC hQC T_C s_C hden_C hcomp_C QD hQD
          (insert (CompletedTensor.inl A B C s_B) (T_B.image (CompletedTensor.inl A B C)) *
            insert (CompletedTensor.inr A B C s_C) (T_C.image (CompletedTensor.inr A B C)))
          (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)
          (CompletedTensor.hasDenominatorPower_inl_mul_inr QD hTB hTC
            (Localization.Away (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)))
          (spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset
            PB PC T_B s_B T_C s_C).symm
          ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)}
      (spaRationalFamily ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) := by
  refine bijOn_preimage_localizedBaseRatLocSpaHomeomorph_spaRationalFamily QA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hcomp_B QC PC hQC T_C s_C hden_C hcomp_C QD hQD
    (insert (CompletedTensor.inl A B C s_B) (T_B.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s_C) (T_C.image (CompletedTensor.inr A B C)))
    (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)
    (CompletedTensor.hasDenominatorPower_inl_mul_inr QD hTB hTC
      (Localization.Away (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)))
    (spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset PB PC T_B s_B T_C s_C).symm
    ?_
  have hdec : inst = Classical.decEq (CompletedTensor A B C) := Subsingleton.elim _ _
  subst hdec
  classical
  exact QD.isOpen_span_insert_mul_insert
    (by
      rw [Finset.coe_image, ← Ideal.map_span]
      exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hTB)
    (by
      rw [Finset.coe_image, ← Ideal.map_span]
      exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hTC)

end LocalizedBaseCanonical

/-! ### Single-factor completed base change `(B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺)` -/

section SingleFactor

variable {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]
  [IsAdicHom (algebraMap A B)]
  (QA : PairOfDefinition A) (PA : Pair A) (hQA : QA.ringOfDefinition ≤ PA.plus)
  (T_A : Finset A) (s_A : A) (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
  (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (T_B : Finset B) (s_B : B) (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
  (hBU : comap (algebraMap A B) ⁻¹' rationalSubset PA.plus T_A s_A ∩ spa PB.plus =
    rationalSubset PB.plus T_B s_B)

omit [IsAdicHom (algebraMap A B)] in
include hBU in
private theorem mapsTo_of_baseChange :
    Set.MapsTo (comap (algebraMap A B))
      (rationalSubset PB.plus T_B s_B) (rationalSubset PA.plus T_A s_A) := by
  rw [← hBU]
  exact fun _ hv ↦ hv.1

/-- Forward morphism of Huber pairs `(B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺) → (B⟨T_B/s_B⟩, B_U⁺)`. -/
noncomputable def baseChangeRatLocHom :
    Hom
      (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A))
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B) :=
  lift
    (toCompletionLocHom QB PB hQB T_B s_B (Localization.Away s_B) hden_B)
    (pairHomOfMapsToRationalSubset QA PA hQA T_A s_A (Localization.Away s_A) hden_A
      QB PB hQB T_B s_B (Localization.Away s_B) hden_B
      (algebraMap A B) (IsAdicHom.continuous inferInstance)
      (mapsTo_of_baseChange PA T_A s_A PB T_B s_B hBU))
    (by
      rw [toRingHom_toCompletionLocHom, toRingHom_pairHomOfMapsToRationalSubset,
        algebraMap_ratLoc QA, ringHomOfMapsToRationalSubset_comp_toCompletionLoc])

include hBU in
private theorem comap_inl_mem_rationalSubset_of_mem_spa_baseChange
    {w : Spv (CompletedTensor A B (ratLoc QA T_A s_A hden_A))}
    (hw : w ∈ spa (PB.completedTensor A
      (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus) :
    comap (CompletedTensor.inl A B (ratLoc QA T_A s_A hden_A)) w ∈
      rationalSubset PB.plus T_B s_B := by
  have hw_cont := ((ValuationSpectrum.mem_spa_iff _ _).mp hw).1
  obtain ⟨hwB, hwA⟩ := (mem_spa_iff PB
    (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A) hw_cont).mp hw
  rw [← hBU]
  refine ⟨?_, hwB⟩
  rw [Set.mem_preimage, comap_comap_apply, CompletedTensor.inl_comp_algebraMap,
    algebraMap_ratLoc QA, ← comap_comap_apply]
  let _ := QA.locUniformSpace T_A s_A (Localization.Away s_A) hden_A
  have _ := QA.isUniformAddGroup_locUniformSpace T_A s_A (Localization.Away s_A) hden_A
  have _ := QA.isTopologicalRing_locUniformSpace T_A s_A (Localization.Away s_A) hden_A
  simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset QA PA.plus T_A s_A (Localization.Away s_A) hden_A
      ⟨comap (CompletedTensor.inr A B (ratLoc QA T_A s_A hden_A)) w, by
        simpa only [rationalLocalizationPair_plus] using hwA⟩

include PA hQA PB hBU in
private theorem existsUnique_baseChangeRatLocSymm :
    ∃! g : ratLoc QB T_B s_B hden_B →+* CompletedTensor A B (ratLoc QA T_A s_A hden_A),
      Continuous g ∧
        g.comp (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B) =
          CompletedTensor.inl A B (ratLoc QA T_A s_A hden_A) :=
  existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    QB PB.plus T_B s_B (Localization.Away s_B) hden_B
    (PB.completedTensor A
      (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus
    (PB.completedTensor A
      (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A)
        hden_A)).isRingOfIntegralElements
    (CompletedTensor.continuous_inl A B (ratLoc QA T_A s_A hden_A)).continuousAt
    fun _ hw ↦ comap_inl_mem_rationalSubset_of_mem_spa_baseChange QA PA hQA T_A s_A hden_A
      PB T_B s_B hBU hw

/-- Inverse morphism of Huber pairs `(B⟨T_B/s_B⟩, B_U⁺) → (B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺)`. -/
noncomputable def baseChangeRatLocSymmHom :
    Hom
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B)
      (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)) where
  toRingHom := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
    QB PB T_B s_B hden_B hBU).choose
  continuous_toRingHom := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
    QB PB T_B s_B hden_B hBU).choose_spec.1.1
  map_mem_plus f hf := by
    let PE := PB.completedTensor A
      (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)
    have hcont := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
      QB PB T_B s_B hden_B hBU).choose_spec.1.1
    have hcomp := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
      QB PB T_B s_B hden_B hBU).choose_spec.1.2
    refine PE.isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
    let _ := QB.locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    have _ := QB.isUniformAddGroup_locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    have _ := QB.isTopologicalRing_locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    have hspa := comap_mem_spa_completedPlusSubring QB PB.plus T_B s_B (Localization.Away s_B)
      hden_B _ hcont ((ValuationSpectrum.mem_spa_iff _ _).mp hw).1
      (by
        rw [hcomp]
        exact comap_inl_mem_rationalSubset_of_mem_spa_baseChange QA PA hQA T_A s_A hden_A
          PB T_B s_B hBU hw)
    rw [rationalLocalizationPair_plus] at hf
    simpa only [comap_vle, map_one] using ((ValuationSpectrum.mem_spa_iff _ _).mp hspa).2 f hf

/-- `baseChangeRatLocHom` followed by `baseChangeRatLocSymmHom` is the identity. -/
@[simp]
theorem baseChangeRatLocSymmHom_comp_baseChangeRatLocHom :
    (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).comp
        (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU) =
      Hom.id _ := by
  have hcomp := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
    QB PB T_B s_B hden_B hBU).choose_spec.1.2
  refine hom_ext ?_ ?_
  · rw [Hom.id_comp, Hom.comp_assoc]
    apply Hom.ext
    simp only [baseChangeRatLocHom, lift_comp_inl, Hom.toRingHom_comp,
      toRingHom_toCompletionLocHom, toRingHom_inl]
    exact hcomp
  · rw [Hom.id_comp]
    apply Hom.ext
    refine completion_locTopology_ringHom_ext_of_continuous QA T_A s_A (Localization.Away s_A)
      hden_A _ _
      (((baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).comp
        _).comp _).continuous_toRingHom
      (inr A _ _).continuous_toRingHom ?_
    have h₁ :
        (((baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).comp
          (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)).comp
          (inr A _ _)).toRingHom.comp
          (QA.toCompletionLoc T_A s_A (Localization.Away s_A) hden_A) =
        ((baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B
          hBU).toRingHom.comp
          (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B)).comp (algebraMap A B) := by
      simp only [baseChangeRatLocHom, Hom.comp_assoc, lift_comp_inr, Hom.toRingHom_comp,
        toRingHom_pairHomOfMapsToRationalSubset, RingHom.comp_assoc,
        ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
    rw [h₁]
    change ((existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
        QB PB T_B s_B hden_B hBU).choose.comp
        (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B)).comp (algebraMap A B) = _
    rw [hcomp, toRingHom_inr, ← algebraMap_ratLoc QA, CompletedTensor.inl_comp_algebraMap]

/-- `baseChangeRatLocSymmHom` followed by `baseChangeRatLocHom` is the identity. -/
@[simp]
theorem baseChangeRatLocHom_comp_baseChangeRatLocSymmHom :
    (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).comp
        (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU) =
      Hom.id _ := by
  have hcomp := (existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
    QB PB T_B s_B hden_B hBU).choose_spec.1.2
  apply Hom.ext
  refine completion_locTopology_ringHom_ext_of_continuous QB T_B s_B (Localization.Away s_B)
    hden_B _ _
    ((baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).comp
      _).continuous_toRingHom
    (Hom.id _).continuous_toRingHom ?_
  rw [Hom.toRingHom_comp, Hom.toRingHom_id, RingHom.id_comp, RingHom.comp_assoc]
  change (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B
      hBU).toRingHom.comp
      ((existsUnique_baseChangeRatLocSymm QA PA hQA T_A s_A hden_A
        QB PB T_B s_B hden_B hBU).choose.comp
        (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B)) = _
  rw [hcomp, ← toRingHom_inl, ← Hom.toRingHom_comp]
  simp only [baseChangeRatLocHom, lift_comp_inl, toRingHom_toCompletionLocHom]

/-- **Single-factor completed base-change ring isomorphism
`B ⊗̂_A A⟨T_A/s_A⟩ ≃+* B⟨T_B/s_B⟩`** whenever `R_B(T_B/s_B)` cuts out
`comap (algebraMap A B) ⁻¹' R_A(T_A/s_A) ∩ Spa(B, B⁺)`. -/
noncomputable def baseChangeRatLocEquiv :
    CompletedTensor A B (ratLoc QA T_A s_A hden_A) ≃+* ratLoc QB T_B s_B hden_B :=
  RingEquiv.ofRingHom
    (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).toRingHom
    (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).toRingHom
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using
        congrArg Hom.toRingHom
          (baseChangeRatLocHom_comp_baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A
            QB PB hQB T_B s_B hden_B hBU))
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using
        congrArg Hom.toRingHom
          (baseChangeRatLocSymmHom_comp_baseChangeRatLocHom QA PA hQA T_A s_A hden_A
            QB PB hQB T_B s_B hden_B hBU))

/-- `baseChangeRatLocEquiv` is continuous. -/
@[fun_prop]
theorem continuous_baseChangeRatLocEquiv :
    Continuous (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU) :=
  (baseChangeRatLocHom QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).continuous_toRingHom

/-- `(baseChangeRatLocEquiv …).symm` is continuous. -/
@[fun_prop]
theorem continuous_baseChangeRatLocEquiv_symm :
    Continuous (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A
      QB PB hQB T_B s_B hden_B hBU).symm :=
  (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hBU).continuous_toRingHom

/-- `baseChangeRatLocEquiv` is a homeomorphism. -/
theorem isHomeomorph_baseChangeRatLocEquiv :
    IsHomeomorph (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU) :=
  (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hBU).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU,
     continuous_baseChangeRatLocEquiv_symm QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU⟩

/-- `baseChangeRatLocEquiv` sends `inl b` to `algebraMap B B⟨T_B/s_B⟩ b`. -/
@[simp]
theorem baseChangeRatLocEquiv_inl (b : B) :
    baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU
        (CompletedTensor.inl A B _ b) =
      algebraMap B (ratLoc QB T_B s_B hden_B) b := by
  rw [algebraMap_ratLoc QB]
  simp [baseChangeRatLocEquiv, baseChangeRatLocHom]

/-- `baseChangeRatLocEquiv` sends `inr (algebraMap A A⟨T_A/s_A⟩ a)` to
`algebraMap B B⟨T_B/s_B⟩ (algebraMap A B a)`. -/
@[simp]
theorem baseChangeRatLocEquiv_inr_algebraMap (a : A) :
    baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU
        (CompletedTensor.inr A B _ (algebraMap A (ratLoc QA T_A s_A hden_A) a)) =
      algebraMap B (ratLoc QB T_B s_B hden_B) (algebraMap A B a) := by
  rw [algebraMap_ratLoc QA, algebraMap_ratLoc QB]
  simpa [baseChangeRatLocEquiv, baseChangeRatLocHom] using
    ringHomOfMapsToRationalSubset_toCompletionLoc QA PA.plus T_A s_A (Localization.Away s_A)
      hden_A QB PB.plus PB.isRingOfIntegralElements.isPowerBounded_of_mem T_B s_B
      (Localization.Away s_B) hden_B (algebraMap A B) (IsAdicHom.continuous inferInstance)
      (mapsTo_of_baseChange PA T_A s_A PB T_B s_B hBU) a

/-- `(baseChangeRatLocEquiv …).symm` sends `algebraMap B B⟨T_B/s_B⟩ b` to `inl b`. -/
@[simp]
theorem baseChangeRatLocEquiv_symm_algebraMap (b : B) :
    (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).symm
        (algebraMap B (ratLoc QB T_B s_B hden_B) b) =
      CompletedTensor.inl A B _ b := by
  apply (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).injective
  simp

/-- **`baseChangeRatLocEquiv` preserves membership in the rings of integral elements in both
directions.** -/
@[simp]
theorem baseChangeRatLocEquiv_mem_plus_iff
    (x : CompletedTensor A B (ratLoc QA T_A s_A hden_A)) :
    baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU x ∈
        (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).plus ↔
      x ∈ (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ (baseChangeRatLocHom QA PA hQA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hBU).map_mem_plus x hx⟩
  have h := (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hBU).map_mem_plus _ hx
  simpa only [show (baseChangeRatLocSymmHom QA PA hQA T_A s_A hden_A
      QB PB hQB T_B s_B hden_B hBU).toRingHom
      (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU x) = x from
    (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A
      QB PB hQB T_B s_B hden_B hBU).symm_apply_apply x] using h

/-- **`baseChangeRatLocEquiv` carries `(PB.completedTensor A A_W).plus` onto `B_U⁺`.** -/
theorem map_baseChangeRatLocEquiv_plus :
    (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus.map
        (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU : _ →+* _) =
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).plus := by
  ext y
  rw [Subring.mem_map_equiv]
  have h := (baseChangeRatLocEquiv_mem_plus_iff QA PA hQA T_A s_A hden_A
    QB PB hQB T_B s_B hden_B hBU
    ((baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A
      QB PB hQB T_B s_B hden_B hBU).symm y)).symm
  simpa using h

/-- **Homeomorphism identifying `Spa((B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺))` with
`R_B(T_B/s_B) ⊆ Spa(B, B⁺)`.** -/
noncomputable def baseChangeRatLocSpaHomeomorph :
    spa (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus ≃ₜ
      (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B : Set (spa PB.plus)) :=
  ((spaHomeomorphOfRingEquiv
      (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
      (continuous_baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
      (continuous_baseChangeRatLocEquiv_symm QA PA hQA T_A s_A hden_A
        QB PB hQB T_B s_B hden_B hBU)
      (map_baseChangeRatLocEquiv_plus QA PA hQA T_A s_A hden_A
        QB PB hQB T_B s_B hden_B hBU)).symm).trans
    (spaRationalLocalizationPairHomeomorph QB PB hQB T_B s_B (Localization.Away s_B) hden_B)

/-- **`baseChangeRatLocSpaHomeomorph` agrees with `(inl A PB A_W).spaComap` into `Spa(B, B⁺)`.** -/
theorem baseChangeRatLocSpaHomeomorph_coe
    (w : spa (PB.completedTensor A
      (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus) :
    (baseChangeRatLocSpaHomeomorph QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU w :
        spa PB.plus) =
      (inl A PB _).spaComap w := by
  apply Subtype.ext
  simp only [baseChangeRatLocSpaHomeomorph, Homeomorph.trans_apply,
    spaRationalLocalizationPairHomeomorph_coe_val, spaHomeomorphOfRingEquiv_symm_val,
    ← algebraMap_ratLoc QB, comap_comap_apply, Hom.spaComap_val, toRingHom_inl]
  have hhom :
      ((baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU).symm :
          ratLoc QB T_B s_B hden_B →+*
            CompletedTensor A B (ratLoc QA T_A s_A hden_A)).comp
        (algebraMap B (ratLoc QB T_B s_B hden_B)) =
      CompletedTensor.inl A B (ratLoc QA T_A s_A hden_A) := by
    ext b
    simp
  rw [hhom]

/-- **Pullback along `baseChangeRatLocSpaHomeomorph` bijects rational subsets of `Spa(B, B⁺)`
contained in `R_B(T_B/s_B)` onto `spaRationalFamily` of `(B, B⁺) ⊗̂_A (A⟨T_A/s_A⟩, A_W⁺)`.** -/
theorem bijOn_preimage_baseChangeRatLocSpaHomeomorph_spaRationalFamily
    (hTB : IsOpen (Ideal.span (T_B : Set B) : Set B)) :
    Set.BijOn (fun W : Set (spa PB.plus) ↦
        baseChangeRatLocSpaHomeomorph QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU ⁻¹'
          (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily PB.plus | W ⊆ Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B}
      (spaRationalFamily (PB.completedTensor A
        (rationalLocalizationPair QA PA hQA T_A s_A (Localization.Away s_A) hden_A)).plus) := by
  have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_symm_spaRationalFamily
    (baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
    (continuous_baseChangeRatLocEquiv QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
    (continuous_baseChangeRatLocEquiv_symm QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
    (map_baseChangeRatLocEquiv_plus QA PA hQA T_A s_A hden_A QB PB hQB T_B s_B hden_B hBU)
  have hbij₂ := bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily
    QB PB hQB T_B s_B hTB (Localization.Away s_B) hden_B
  refine (hbij₁.comp hbij₂).congr fun W _ ↦ ?_
  ext w
  simp [baseChangeRatLocSpaHomeomorph]

end SingleFactor

/-! ### Degenerate (`s_B = 0`) and discrete non-vacuity checks -/

section NonVacuity

section DenomZero

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

/-- **Degenerate denominator `s_B = 0`.** When `s_B = 0`, `0` becomes invertible in `B⟨T_B/0⟩`, so
the localized-base completed tensor ring `B⟨T_B/0⟩ ⊗̂_{A⟨T_A/s_A⟩} C⟨T_C/s_C⟩` is subsingleton and
its adic spectrum is empty. -/
theorem subsingleton_and_spa_eq_empty_of_denom_zero
    (QA : PairOfDefinition A) (PA : Pair A)
    (T_A : Finset A) (s_A : A) (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
    (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
    (T_B : Finset B) (hden_B : QB.HasDenominatorPower T_B 0 (Localization.Away (0 : B)))
    (hmaps_B : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset PB.plus T_B 0) (rationalSubset PA.plus T_A s_A))
    (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
    (T_C : Finset C) (s_C : C) (hden_C : QC.HasDenominatorPower T_C s_C (Localization.Away s_C))
    (hmaps_C : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset PC.plus T_C s_C) (rationalSubset PA.plus T_A s_A)) :
    letI := Pair.ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B 0 hden_B hmaps_B
    letI := Pair.isAdicHom_ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B 0 hden_B hmaps_B
    letI := Pair.ratLocAlgebra PA QA T_A s_A hden_A PC QC T_C s_C hden_C hmaps_C
    letI := Pair.isAdicHom_ratLocAlgebra PA QA T_A s_A hden_A PC QC T_C s_C hden_C hmaps_C
    Subsingleton (CompletedTensor (ratLoc QA T_A s_A hden_A)
      (ratLoc QB T_B 0 hden_B) (ratLoc QC T_C s_C hden_C)) ∧
      spa ((rationalLocalizationPair QB PB hQB T_B 0 (Localization.Away (0 : B))
        hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus = ∅ := by
  let _ := Pair.ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B 0 hden_B hmaps_B
  have _ := Pair.isAdicHom_ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B 0 hden_B hmaps_B
  let _ := Pair.ratLocAlgebra PA QA T_A s_A hden_A PC QC T_C s_C hden_C hmaps_C
  have _ := Pair.isAdicHom_ratLocAlgebra PA QA T_A s_A hden_A PC QC T_C s_C hden_C hmaps_C
  have hB : Subsingleton (ratLoc QB T_B 0 hden_B) := by
    obtain ⟨u, hu⟩ := isUnit_algebraMap_ratLoc QB T_B 0 hden_B
    rw [map_zero] at hu
    exact subsingleton_iff_zero_eq_one.mp (by rw [← u.mul_inv, hu, zero_mul])
  have hE : Subsingleton (CompletedTensor (ratLoc QA T_A s_A hden_A)
      (ratLoc QB T_B 0 hden_B) (ratLoc QC T_C s_C hden_C)) :=
    subsingleton_iff_zero_eq_one.mp <| by
      rw [← map_one (CompletedTensor.inl (ratLoc QA T_A s_A hden_A)
        (ratLoc QB T_B 0 hden_B) (ratLoc QC T_C s_C hden_C)),
        Subsingleton.elim (1 : ratLoc QB T_B 0 hden_B) 0, map_zero]
  exact ⟨hE, (spa_eq_empty_iff_subsingleton _
    ((rationalLocalizationPair QB PB hQB T_B 0 (Localization.Away (0 : B))
      hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
      (rationalLocalizationPair QC PC hQC T_C s_C
        (Localization.Away s_C) hden_C)).isRingOfIntegralElements).mpr hE⟩

end DenomZero

section DiscreteNonVacuity

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

private theorem mapsTo_discrete_unit
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] :
    Set.MapsTo (comap (algebraMap R (R × R)))
      (rationalSubset (Pair.discrete (R × R)).plus ({1} : Finset (R × R)) 1)
      (rationalSubset (Pair.discrete R).plus ({1} : Finset R) 1) := by
  rw [rationalSubset_singleton_one, rationalSubset_singleton_one]
  exact fun _ hv ↦ comap_mem_spa continuous_of_discreteTopology (fun _ _ ↦ by simp) hv

/-- **Non-vacuity check over a nontrivial discrete ring.** For any nontrivial discrete commutative
ring `R`, taking `B = C = R × R` over `A = R` with unit presentations `({1}, 1)` exercises
`Pair.ratLocAlgebra`, `localizedBaseRatLocEquiv`, and `localizedBaseRatLocSpaHomeomorph` on a
genuinely nontrivial completed tensor ring with nonempty adic spectrum. -/
theorem nontrivial_and_spa_nonempty_localizedBase_of_discrete
    (R : Type u) [CommRing R] [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] :
    letI : IsAdicHom (algebraMap R (R × R)) := IsAdicHom.of_discrete_iff.mpr inferInstance
    ∃ (QA : PairOfDefinition R) (PA : Pair R) (T_A : Finset R) (s_A : R)
      (hden_A : QA.HasDenominatorPower T_A s_A (Localization.Away s_A))
      (QB : PairOfDefinition (R × R)) (PB : Pair (R × R)) (hQB : QB.ringOfDefinition ≤ PB.plus)
      (T_B : Finset (R × R)) (s_B : R × R)
      (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
      (hmaps_B : Set.MapsTo (comap (algebraMap R (R × R)))
        (rationalSubset PB.plus T_B s_B) (rationalSubset PA.plus T_A s_A)),
      letI := Pair.ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B s_B hden_B hmaps_B
      letI := Pair.isAdicHom_ratLocAlgebra PA QA T_A s_A hden_A PB QB T_B s_B hden_B hmaps_B
      Nontrivial (CompletedTensor (ratLoc QA T_A s_A hden_A)
        (ratLoc QB T_B s_B hden_B) (ratLoc QB T_B s_B hden_B)) ∧
        (spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
          hden_B).completedTensor (ratLoc QA T_A s_A hden_A)
          (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
            hden_B)).plus).Nonempty := by
  have _ : IsAdicHom (algebraMap R (R × R)) := IsAdicHom.of_discrete_iff.mpr inferInstance
  let QA : PairOfDefinition R := PairOfDefinition.discrete R
  let PA : Pair R := Pair.discrete R
  let QB : PairOfDefinition (R × R) := PairOfDefinition.discrete (R × R)
  let PB : Pair (R × R) := Pair.discrete (R × R)
  have hQB : QB.ringOfDefinition ≤ PB.plus := by simp [QB, PB]
  let T_A : Finset R := {1}
  let T_B : Finset (R × R) := {1}
  let hden_A : QA.HasDenominatorPower T_A 1 (Localization.Away (1 : R)) :=
    QA.hasDenominatorPower_of_isOpen_span (T_A : Set R) 1 (Localization.Away (1 : R))
      (isOpen_discrete _)
  let hden_B : QB.HasDenominatorPower T_B 1 (Localization.Away (1 : R × R)) :=
    QB.hasDenominatorPower_of_isOpen_span (T_B : Set (R × R)) 1 (Localization.Away (1 : R × R))
      (isOpen_discrete _)
  have hmaps_B : Set.MapsTo (comap (algebraMap R (R × R)))
      (rationalSubset PB.plus T_B 1) (rationalSubset PA.plus T_A 1) :=
    mapsTo_discrete_unit R
  let _ := Pair.ratLocAlgebra PA QA T_A 1 hden_A PB QB T_B 1 hden_B hmaps_B
  have _ := Pair.isAdicHom_ratLocAlgebra PA QA T_A 1 hden_A PB QB T_B 1 hden_B hmaps_B
  have hcomp_B := PA.algebraMap_ratLocAlgebra_comp QA T_A 1 hden_A PB QB T_B 1 hden_B hmaps_B
  have _ : DiscreteTopology (CompletedTensor R (R × R) (R × R)) :=
    IsAdicHom.of_discrete_iff.mp (CompletedTensor.isAdicHom_inl R (R × R) (R × R))
  obtain ⟨QD, hQD⟩ := exists_pairOfDefinition_ringOfDefinition_le
    (PB.completedTensor R PB).isRingOfIntegralElements.isOpen
  let T_D : Finset (CompletedTensor R (R × R) (R × R)) := {1}
  let hden_D : QD.HasDenominatorPower T_D 1
      (Localization.Away (1 : CompletedTensor R (R × R) (R × R))) :=
    QD.hasDenominatorPower_of_isOpen_span (T_D : Set _) 1 _ (isOpen_discrete _)
  have hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor R PB).plus T_D 1 :
      Set (spa (PB.completedTensor R PB).plus)) =
      (inl R PB PB).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B 1) ∩
        (inr R PB PB).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B 1) := by
    simp [T_D, T_B, Subtype.coe_preimage_self]
  have hR_nonempty : (spa PA.plus).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h ↦
      not_subsingleton R ((spa_eq_empty_iff_subsingleton PA.plus PA.isRingOfIntegralElements).mp h)
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have _ : DiscreteUniformity R := IsRightUniformAddGroup.discreteUniformity
  let fstHom : Hom PB PA :=
    { toRingHom := RingHom.fst R R
      continuous_toRingHom := continuous_fst
      map_mem_plus := fun _ _ ↦ by simp [PA] }
  let projHom : Hom (PB.completedTensor R PB) PA :=
    lift fstHom fstHom rfl
  obtain ⟨v₀, hv₀⟩ := hR_nonempty
  have hinter_nonempty :
      ((inl R PB PB).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B 1) ∩
        (inr R PB PB).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B 1)).Nonempty :=
    ⟨projHom.spaComap ⟨v₀, hv₀⟩, by simp [T_B, Subtype.coe_preimage_self]⟩
  have hspa_nonempty := (localizedBaseRatLoc_spa_nonempty_iff QA T_A 1 hden_A
    QB PB hQB T_B 1 hden_B hcomp_B QB PB hQB T_B 1 hden_B hcomp_B
    QD hQD T_D 1 hden_D hUV).mpr hinter_nonempty
  have hNontrivial : Nontrivial (CompletedTensor (ratLoc QA T_A 1 hden_A)
      (ratLoc QB T_B 1 hden_B) (ratLoc QB T_B 1 hden_B)) :=
    (subsingleton_or_nontrivial _).resolve_left fun hsub ↦
      hspa_nonempty.ne_empty ((spa_eq_empty_iff_subsingleton _
        ((rationalLocalizationPair QB PB hQB T_B 1 (Localization.Away (1 : R × R))
          hden_B).completedTensor (ratLoc QA T_A 1 hden_A)
          (rationalLocalizationPair QB PB hQB T_B 1 (Localization.Away (1 : R × R))
            hden_B)).isRingOfIntegralElements).mpr hsub)
  exact ⟨QA, PA, T_A, 1, hden_A, QB, PB, hQB, T_B, 1, hden_B, hmaps_B,
    hNontrivial, hspa_nonempty⟩

end DiscreteNonVacuity

end NonVacuity

end Pair.completedTensor

end TauCeti.Huber

end
