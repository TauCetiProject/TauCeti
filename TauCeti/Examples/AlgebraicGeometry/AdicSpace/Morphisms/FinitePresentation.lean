/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Comparison
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Examples for morphisms locally of finite type and locally of finite presentation

Concrete instantiations exercising `TauCeti.AdicSpace.LocallyOfFiniteType` and
`TauCeti.AdicSpace.LocallyOfFinitePresentation`: relative `p`-adic polydiscs, rational polydisc
sections via right-cancellation, analytic-locus upgrades, discrete quotients (`ℤ →+* ZMod 6`),
non-noetherian discrete separation (`ℤ[X₀, X₁, …] →+* ℤ`), and morphisms out of `Spa(0, 0)`.
-/

open CategoryTheory TopologicalSpace
open TauCeti TauCeti.Huber TauCeti.PreAdicSpace TauCeti.ValuationSpectrum TauCeti.AdicSpace

namespace FinitePresentationChecks

universe u

/-- Relative `p`-adic polydisc projection. -/
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let S := Pair.powerBounded ℚ_[p]
    let T := S.polydisc n
    have hn := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) n)
      |>.isTopologicallyFiniteType
    have := hn.isTateRing; have := hn.isStronglyNoetherian
    let φ : S.Hom T := S.weightedCompletionHom isWeightFamily_one_weight
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    let hT := isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ∧
      (ofPair T hT).IsLocallyHuberStandard ∧ (ofPair T hT).IsLocallyNoetherian := by
  intro S T hn _ _ φ hS hT
  have hlfp := locallyOfFinitePresentation_comapOfPair_of_isStronglyNoetherian hS hT φ
    (S.isTopologicallyFiniteType_weightedCompletionHom (fun _ ↦ Set.finite_singleton 1)
      isWeightFamily_one_weight)
  exact ⟨hlfp, hlfp.isLocallyHuberStandard_source, hlfp.isLocallyNoetherian_source⟩

/-- Right-cancellation on rational sections of the `p`-adic polydisc via `of_comp`. -/
example (p : ℕ) [Fact p.Prime] (n : ℕ) (t : Fin n → (Pair.powerBounded ℚ_[p]).plus) :
    let S := Pair.powerBounded ℚ_[p]
    let T := S.polydisc n
    have hn := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) n)
      |>.isTopologicallyFiniteType
    have := hn.isTateRing; have := hn.isStronglyNoetherian
    let ev : T.Hom S := Pair.polydisc.evalHom (Pair.Hom.id S) t
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    let hT := isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements
    LocallyOfFinitePresentation (comapOfPair hT hS ev) := by
  intro S T hn _ _ ev hS hT
  let φ : S.Hom T := S.weightedCompletionHom isWeightFamily_one_weight
  have hπ := locallyOfFinitePresentation_comapOfPair_of_isStronglyNoetherian hS hT φ
    (S.isTopologicallyFiniteType_weightedCompletionHom (fun _ ↦ Set.finite_singleton 1)
      isWeightFamily_one_weight)
  have hsec : comapOfPair hT hS ev ≫ comapOfPair hS hT φ = 𝟙 (ofPair S hS) := by
    rw [← comapOfPair_comp hS hT hS φ ev, Pair.polydisc.evalHom_comp_weightedCompletionHom,
      comapOfPair_id]
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  have hStdS := (IsLocallyHuberStandard.spa P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP (hS.isSheaf P hP)).of_isOpenImmersion
    (ofPairIsoOfPresentation S hS P hP).hom
  exact .of_comp (hsec.symm ▸ .id hStdS) hπ.locallyOfFiniteType

/-- Analytic-locus upgrade for morphisms locally of finite type into a locally noetherian target. -/
example {X Y : AdicSpace.{u}} {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (hY : Y.IsLocallyNoetherian) : LocallyOfFinitePresentation hf.isAdic.analyticLocusMap :=
  hf.locallyOfFinitePresentation_analyticLocusMap hY

/-- Discrete finite quotient `ℤ →+* ZMod 6`. -/
example [TopologicalSpace ℤ] [DiscreteTopology ℤ] [TopologicalSpace (ZMod 6)]
    [DiscreteTopology (ZMod 6)] (hZ : IsSheafyForEveryPresentation (Pair.discrete ℤ).plus)
    (hQ : IsSheafyForEveryPresentation (Pair.discrete (ZMod 6)).plus) :
    haveI : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
    haveI : IsTopologicalRing (ZMod 6) := DiscreteTopology.topologicalRing
    let φ := Pair.Hom.ofDiscrete (Int.castRingHom (ZMod 6))
    φ.IsTopologicallyFiniteType ∧ LocallyOfFinitePresentation (comapOfPair hZ hQ φ) := by
  have : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
  have : IsTopologicalRing (ZMod 6) := DiscreteTopology.topologicalRing
  intro φ
  have hft : φ.toRingHom.FiniteType := by
    rw [Pair.Hom.toRingHom_ofDiscrete]
    exact RingHom.FiniteType.of_surjective _ ZMod.intCast_surjective
  exact ⟨Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete.mpr hft,
    (locallyOfFinitePresentation_comapOfPair_discrete_iff hZ hQ φ).mpr
      (RingHom.FinitePresentation.of_finiteType.mp hft)⟩

/-- Separation of `LocallyOfFiniteType` and `LocallyOfFinitePresentation` via `ℤ[X₀, X₁, …] →+* ℤ`.
-/
example [TopologicalSpace (MvPolynomial ℕ ℤ)] [DiscreteTopology (MvPolynomial ℕ ℤ)]
    [TopologicalSpace ℤ] [DiscreteTopology ℤ]
    (hR : IsSheafyForEveryPresentation (Pair.discrete (MvPolynomial ℕ ℤ)).plus)
    (hZ : IsSheafyForEveryPresentation (Pair.discrete ℤ).plus) :
    haveI : IsTopologicalRing (MvPolynomial ℕ ℤ) := DiscreteTopology.topologicalRing
    haveI : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
    let aug : MvPolynomial ℕ ℤ →+* ℤ := MvPolynomial.constantCoeff
    let φ := Pair.Hom.ofDiscrete aug
    φ.IsTopologicallyFiniteType ∧ LocallyOfFiniteType (comapOfPair hR hZ φ) ∧
      ¬ LocallyOfFinitePresentation (comapOfPair hR hZ φ) := by
  have : IsTopologicalRing (MvPolynomial ℕ ℤ) := DiscreteTopology.topologicalRing
  have : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
  intro aug φ
  have hsurj : Function.Surjective aug := fun m ↦ ⟨MvPolynomial.C m, by simp [aug]⟩
  have hft : φ.toRingHom.FiniteType := by
    rw [Pair.Hom.toRingHom_ofDiscrete]
    exact RingHom.FiniteType.of_surjective aug hsurj
  refine ⟨Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete.mpr hft,
    (locallyOfFiniteType_comapOfPair_discrete_iff hR hZ φ).mpr hft, fun hlfp ↦ ?_⟩
  have hfp : aug.FinitePresentation := by
    simpa [φ] using (locallyOfFinitePresentation_comapOfPair_discrete_iff hR hZ φ).mp hlfp
  let _ : Algebra (MvPolynomial ℕ ℤ) ℤ := aug.toAlgebra
  have : Algebra.FinitePresentation (MvPolynomial ℕ ℤ) ℤ := hfp
  have hfg : (RingHom.ker aug).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId (MvPolynomial ℕ ℤ) ℤ) hsurj
  rw [MvPolynomial.ker_constantCoeff] at hfg
  exact MvPolynomial.not_fg_idealOfVars ℕ ℤ hfg

/-- Empty source: any morphism out of `Spa(0, 0)` is locally of finite presentation. -/
example {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [Subsingleton A] {S : Pair A} (hS : IsSheafyForEveryPresentation S.plus) {Y : AdicSpace.{u}}
    (f : ofPair S hS ⟶ Y) : LocallyOfFinitePresentation f := by
  have : IsEmpty (ofPair S hS).obj := ⟨fun z ↦ by
    have hz := (spa_eq_empty_iff_subsingleton S.plus S.isRingOfIntegralElements).mpr inferInstance
    obtain ⟨_, hm⟩ := ofPairHomeomorph S hS z
    rw [hz] at hm
    exact hm⟩
  exact LocallyOfFinitePresentation.of_isEmpty f

end FinitePresentationChecks
