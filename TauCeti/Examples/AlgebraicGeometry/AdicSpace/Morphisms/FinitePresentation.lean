/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Comparison
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

/-!
# Examples for morphisms locally of finite type and locally of finite presentation

Concrete positive checks and a discrete non-noetherian separation check exercising
`TauCeti.AdicSpace.LocallyOfFiniteType` and `TauCeti.AdicSpace.LocallyOfFinitePresentation`:

1. **`p`-adic polydiscs**: for any prime `p` and `n : ℕ`, the structure morphism
   `Spa(ℚ_[p]⟨T₁, …, Tₙ⟩, ℤ_[p]⟨T₁, …, Tₙ⟩) ⟶ Spa(ℚ_[p], ℤ_[p])` is unconditionally locally of
   finite presentation, and its source is locally of Huber's standing class and locally noetherian.
2. **Right-cancellation on rational sections**: for any prime `p`, dimension `n : ℕ`, and rational
   point `t : Fin n → (Pair.powerBounded ℚ_[p]).plus`, the section
   `Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T₁, …, Tₙ⟩, ℤ_[p]⟨T₁, …, Tₙ⟩)` induced by evaluation at `t` is
   proved locally of finite presentation directly via `LocallyOfFinitePresentation.of_comp`, without
   constructing a weighted polynomial presentation for the evaluation map.
3. **Analytic-locus upgrade**: any morphism locally of finite type into a locally noetherian adic
   space restricts to a morphism locally of finite presentation on analytic loci.
4. **Discrete finite quotient**: `ℤ →+* ZMod 6` induces a morphism locally of finite presentation
   between discrete adic spectra.
5. **Non-example separating `LocallyOfFiniteType` from `LocallyOfFinitePresentation`**: over the
   discrete polynomial ring `ℤ[X₀, X₁, …]` in countably many variables, the augmentation
   `aug : ℤ[X₀, X₁, …] →+* ℤ` (`Xᵢ ↦ 0`) is surjective and hence topologically of finite type,
   inducing a morphism **locally of finite type** `Spa(ℤ, ℤ) ⟶ Spa(ℤ[X₀, X₁, …], ℤ[X₀, X₁, …])`,
   whereas its kernel is not finitely generated so the induced morphism is **not** locally of
   finite presentation.
6. **Empty source**: any morphism out of `Spa(0, 0)` is locally of finite presentation.
-/

open CategoryTheory TopologicalSpace
open TauCeti TauCeti.Huber TauCeti.PreAdicSpace TauCeti.ValuationSpectrum TauCeti.AdicSpace

namespace FinitePresentationChecks

universe u

/-- **Relative `p`-adic polydisc**: for any prime `p` and `n : ℕ`, the projection
`Spa(ℚ_[p]⟨T₁, …, Tₙ⟩, ℤ_[p]⟨T₁, …, Tₙ⟩) ⟶ Spa(ℚ_[p], ℤ_[p])` is unconditionally locally of finite
presentation, and its source is locally of Huber's standing class and locally noetherian. -/
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let S := Pair.powerBounded ℚ_[p]
    let T := S.polydisc n
    have hn := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) n)
      |>.isTopologicallyFiniteType
    have := hn.isTateRing
    have := hn.isStronglyNoetherian
    let φ : S.Hom T := S.weightedCompletionHom isWeightFamily_one_weight
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    let hT := isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ∧
      (ofPair T hT).IsLocallyHuberStandard ∧
      (ofPair T hT).IsLocallyNoetherian := by
  intro S T hn _ _ φ hS hT
  have hφ : φ.IsTopologicallyFiniteType :=
    S.isTopologicallyFiniteType_weightedCompletionHom (fun _ ↦ Set.finite_singleton 1)
      isWeightFamily_one_weight
  have hlfp : LocallyOfFinitePresentation (comapOfPair hS hT φ) :=
    locallyOfFinitePresentation_comapOfPair_of_isTateRing hS hT φ hφ
  exact ⟨hlfp, hlfp.isLocallyHuberStandard_source, hlfp.isLocallyNoetherian_source⟩

/-- **Right-cancellation on rational sections**: for any prime `p`, `n : ℕ`, and coordinate tuple
`t : Fin n → (Pair.powerBounded ℚ_[p]).plus`, the section
`Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T₁, …, Tₙ⟩, ℤ_[p]⟨T₁, …, Tₙ⟩)` induced by `Pair.polydisc.evalHom`
is locally of finite presentation via `LocallyOfFinitePresentation.of_comp`. -/
example (p : ℕ) [Fact p.Prime] (n : ℕ) (t : Fin n → (Pair.powerBounded ℚ_[p]).plus) :
    let S := Pair.powerBounded ℚ_[p]
    let T := S.polydisc n
    have hn := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) n)
      |>.isTopologicallyFiniteType
    have := hn.isTateRing
    have := hn.isStronglyNoetherian
    let ev : T.Hom S := Pair.polydisc.evalHom (Pair.Hom.id S) t
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    let hT := isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements
    LocallyOfFinitePresentation (comapOfPair hT hS ev) := by
  intro S T hn _ _ ev hS hT
  let φ : S.Hom T := S.weightedCompletionHom isWeightFamily_one_weight
  have hφ : φ.IsTopologicallyFiniteType :=
    S.isTopologicallyFiniteType_weightedCompletionHom (fun _ ↦ Set.finite_singleton 1)
      isWeightFamily_one_weight
  have hπ_lfp : LocallyOfFinitePresentation (comapOfPair hS hT φ) :=
    locallyOfFinitePresentation_comapOfPair_of_isTateRing hS hT φ hφ
  have hsec : comapOfPair hT hS ev ≫ comapOfPair hS hT φ = 𝟙 (ofPair S hS) := by
    rw [← comapOfPair_comp hS hT hS φ ev,
      Pair.polydisc.evalHom_comp_weightedCompletionHom, comapOfPair_id]
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  have hStdS : (ofPair S hS).IsLocallyHuberStandard :=
    (IsLocallyHuberStandard.spa P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP
      (hS.isSheaf P hP)).of_isOpenImmersion (ofPairIsoOfPresentation S hS P hP).hom
  exact LocallyOfFinitePresentation.of_comp
    (hsec.symm ▸ LocallyOfFinitePresentation.of_id hStdS) hπ_lfp.locallyOfFiniteType

/-- **Analytic-locus upgrade**: any morphism locally of finite type into a locally noetherian adic
space restricts to a morphism locally of finite presentation on analytic loci. -/
example {X Y : AdicSpace.{u}} {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (hY : Y.IsLocallyNoetherian) :
    LocallyOfFinitePresentation hf.isAdic.analyticLocusMap :=
  hf.locallyOfFinitePresentation_analyticLocusMap hY

/-- **Discrete finite quotient**: `ℤ →+* ZMod 6` is finitely presented and induces a morphism
locally of finite presentation between discrete adic spectra. -/
example [TopologicalSpace ℤ] [DiscreteTopology ℤ]
    [TopologicalSpace (ZMod 6)] [DiscreteTopology (ZMod 6)]
    (hZ : IsSheafyForEveryPresentation (Pair.discrete ℤ).plus)
    (hQ : IsSheafyForEveryPresentation (Pair.discrete (ZMod 6)).plus) :
    haveI : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
    haveI : IsTopologicalRing (ZMod 6) := DiscreteTopology.topologicalRing
    let φ := Pair.Hom.ofDiscrete (Int.castRingHom (ZMod 6))
    φ.IsTopologicallyFiniteType ∧
      LocallyOfFinitePresentation (comapOfPair hZ hQ φ) := by
  have : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
  have : IsTopologicalRing (ZMod 6) := DiscreteTopology.topologicalRing
  intro φ
  have hft : φ.toRingHom.FiniteType := by
    rw [Pair.Hom.toRingHom_ofDiscrete]
    exact RingHom.FiniteType.of_surjective _ ZMod.intCast_surjective
  have hfp : φ.toRingHom.FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp hft
  exact ⟨Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete.mpr hft,
    (locallyOfFinitePresentation_comapOfPair_discrete_iff hZ hQ φ).mpr hfp⟩

/-- **Separation of `LocallyOfFiniteType` and `LocallyOfFinitePresentation` over discrete
non-noetherian rings**: the augmentation `aug : MvPolynomial ℕ ℤ →+* ℤ` (`Xᵢ ↦ 0`) is topologically
of finite type on discrete Huber pairs and induces a morphism **locally of finite type**
`Spa(ℤ, ℤ) ⟶ Spa(ℤ[X₀, X₁, …], ℤ[X₀, X₁, …])` that is **not** locally of finite presentation. -/
example [TopologicalSpace (MvPolynomial ℕ ℤ)] [DiscreteTopology (MvPolynomial ℕ ℤ)]
    [TopologicalSpace ℤ] [DiscreteTopology ℤ]
    (hR : IsSheafyForEveryPresentation (Pair.discrete (MvPolynomial ℕ ℤ)).plus)
    (hZ : IsSheafyForEveryPresentation (Pair.discrete ℤ).plus) :
    haveI : IsTopologicalRing (MvPolynomial ℕ ℤ) := DiscreteTopology.topologicalRing
    haveI : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
    let aug : MvPolynomial ℕ ℤ →+* ℤ := (MvPolynomial.aeval (fun _ : ℕ ↦ (0 : ℤ))).toRingHom
    let φ := Pair.Hom.ofDiscrete aug
    φ.IsTopologicallyFiniteType ∧
      LocallyOfFiniteType (comapOfPair hR hZ φ) ∧
      ¬ LocallyOfFinitePresentation (comapOfPair hR hZ φ) := by
  classical
  have : IsTopologicalRing (MvPolynomial ℕ ℤ) := DiscreteTopology.topologicalRing
  have : IsTopologicalRing ℤ := DiscreteTopology.topologicalRing
  intro aug φ
  have hsurj : Function.Surjective aug := fun m ↦
    ⟨MvPolynomial.C m, by simp [aug]⟩
  have hft : φ.toRingHom.FiniteType := by
    rw [Pair.Hom.toRingHom_ofDiscrete]
    exact RingHom.FiniteType.of_surjective aug hsurj
  have htft : φ.IsTopologicallyFiniteType :=
    Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete.mpr hft
  have hlft : LocallyOfFiniteType (comapOfPair hR hZ φ) :=
    (locallyOfFiniteType_comapOfPair_discrete_iff hR hZ φ).mpr hft
  refine ⟨htft, hlft, fun hlfp ↦ ?_⟩
  have hfp : aug.FinitePresentation := by
    have h := (locallyOfFinitePresentation_comapOfPair_discrete_iff hR hZ φ).mp hlfp
    rwa [Pair.Hom.toRingHom_ofDiscrete] at h
  let _ : Algebra (MvPolynomial ℕ ℤ) ℤ := aug.toAlgebra
  have : Algebra.FinitePresentation (MvPolynomial ℕ ℤ) ℤ := hfp
  have hfg : (RingHom.ker (Algebra.ofId (MvPolynomial ℕ ℤ) ℤ).toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId (MvPolynomial ℕ ℤ) ℤ) hsurj
  have hker_eq : (Algebra.ofId (MvPolynomial ℕ ℤ) ℤ).toRingHom = aug := rfl
  rw [hker_eq] at hfg
  obtain ⟨s, hs⟩ := hfg
  let N : ℕ := (s.biUnion MvPolynomial.vars).sup id + 1
  have hN_not_mem : ∀ g ∈ s, N ∉ g.vars := by
    intro g hg hNg
    have hmem : N ∈ s.biUnion MvPolynomial.vars := Finset.mem_biUnion.mpr ⟨g, hg, hNg⟩
    have hle : N ≤ (s.biUnion MvPolynomial.vars).sup id := Finset.le_sup (f := id) hmem
    omega
  have hXN_ker : MvPolynomial.X N ∈ Ideal.span (s : Set (MvPolynomial ℕ ℤ)) := by
    rw [hs, RingHom.mem_ker]
    simp [aug]
  have hvan : aug (MvPolynomial.X N) = 0 ∧
      aug (MvPolynomial.pderiv N (MvPolynomial.X N)) = 0 := by
    refine Submodule.span_induction (p := fun f _ ↦ aug f = 0 ∧ aug (MvPolynomial.pderiv N f) = 0)
      (fun g hg ↦ ⟨?_, ?_⟩) ⟨by simp, by simp⟩
      (fun x y _ _ hx hy ↦ ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩)
      (fun r x _ hx ↦ ⟨by simp [smul_eq_mul, hx.1],
        by simp [smul_eq_mul, Derivation.leibniz, hx.1, hx.2]⟩) hXN_ker
    · have hg' : g ∈ RingHom.ker aug := hs ▸ Submodule.subset_span hg
      exact RingHom.mem_ker.mp hg'
    · rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars (hN_not_mem g hg), map_zero]
  have h1 : aug (MvPolynomial.pderiv N (MvPolynomial.X N)) = 1 := by
    rw [MvPolynomial.pderiv_X_self, map_one]
  omega

/-- **Empty source**: any morphism out of the adic spectrum of a complete Hausdorff zero Huber pair
is locally of finite presentation. -/
example {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] [Subsingleton A]
    {S : Pair A} (hS : IsSheafyForEveryPresentation S.plus)
    {Y : AdicSpace.{u}} (f : ofPair S hS ⟶ Y) :
    LocallyOfFinitePresentation f := by
  have : IsEmpty (ofPair S hS).obj := ⟨fun z ↦ by
    have hz : spa S.plus = ∅ :=
      (spa_eq_empty_iff_subsingleton S.plus S.isRingOfIntegralElements).mpr inferInstance
    obtain ⟨_, hm⟩ := ofPairHomeomorph S hS z
    rw [hz] at hm
    exact hm⟩
  exact LocallyOfFinitePresentation.of_isEmpty f

end FinitePresentationChecks
