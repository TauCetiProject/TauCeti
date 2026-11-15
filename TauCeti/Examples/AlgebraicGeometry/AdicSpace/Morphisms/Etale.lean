/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Etale
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Pair
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Huber.ModuleTopology.Pair
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.NoetherianType.Tate
import TauCeti.RingTheory.Huber.Padic.TateAlgebra
import TauCeti.RingTheory.Huber.Prod
import TauCeti.RingTheory.Huber.Restricted.OneVariable

/-!
# Examples of finite étale and étale morphisms of analytic adic spaces

Concrete positive and negative examples for `TauCeti.AdicSpace.IsFiniteEtale` and
`TauCeti.AdicSpace.IsEtaleLocalDescription` over `ℚ_[p]`:

* the identities on `Spa(ℚ_[p], ℤ_[p])` and `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale and étale,
  whereas (conditional on sheafiness `hs` of its structure presheaf) the identity on the
  non-analytic space `Spa(ℤ_[p], ℤ_[p])` is neither;
* any morphism from `Spa(0, 0)` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is finite étale, étale, and not
  surjective;
* the rational open immersion `{|T| ≤ |p|} ↪ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is étale
  (`of_isOpenImmersion`) and not finite étale (`η_{|p|} ⤳ η_{|p|⁺}`);
* the trivial double cover `Spa(A × A, (A × A)°) ⟶ Spa(A, A°)` of the closed unit disc is finite
  étale and étale;
* neither the squaring map `T ↦ S²` (for any prime `p`, including `p = 2`) nor the origin closed
  immersion `T ↦ 0` on `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is étale or finite étale, obstructed by
  `eq_of_sqZero_quotient` and `exists_of_sqZero_quotient` against `ℚ_[p]⟨X⟩ ⧸ (X²)`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology UniformSpace IsLocalRing

namespace TauCeti.AdicSpace.Examples

open Huber PreAdicSpace ValuationSpectrum

variable (p : ℕ) [Fact p.Prime]

/-- The identities on `Spa(ℚ_[p], ℤ_[p])` and `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale and
étale. -/
example :
    let S₀ := Pair.powerBounded ℚ_[p]
    let S₁ := S₀.polydisc 1
    let X₀ := AdicSpace.ofPair S₀
      (isSheafyForEveryPresentation_of_isStronglyNoetherian S₀.isRingOfIntegralElements)
    let X₁ := AdicSpace.ofPair S₁
      (isSheafyForEveryPresentation_of_isStronglyNoetherian S₁.isRingOfIntegralElements)
    IsFiniteEtale (𝟙 X₀) ∧ IsEtaleLocalDescription (𝟙 X₀) ∧
      IsFiniteEtale (𝟙 X₁) ∧ IsEtaleLocalDescription (𝟙 X₁) :=
  ⟨.id (IsAnalytic.ofPair _ _), .id (IsAnalytic.ofPair _ _),
    .id (IsAnalytic.ofPair _ _), .id (IsAnalytic.ofPair _ _)⟩

/-- Conditional on sheafiness of its structure presheaf (`hs`), `Spa(ℤ_[p], ℤ_[p])` is not analytic,
so its identity is neither finite étale nor étale. -/
example
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa (⊤ : Subring ℤ_[p])))
      (presentationLimitPresheaf
        (PairOfDefinition.adic (maximalIdeal ℤ_[p]) PadicInt.isAdic_maximalIdeal
          (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _))
        (⊤ : Subring ℤ_[p]))) :
    let P := PairOfDefinition.adic (maximalIdeal ℤ_[p]) PadicInt.isAdic_maximalIdeal
      (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _)
    let hpb : ∀ ⦃a : ℤ_[p]⦄, a ∈ (⊤ : Subring ℤ_[p]) → IsPowerBounded a :=
      fun a _ ↦ IsPowerBounded.of_norm_le_one (_root_.PadicInt.norm_le_one a)
    let X : AdicSpace.{0} := ⟨presentationLimitPreAdicSpace P ⊤ hpb le_top,
      isAdic_presentationLimitPreAdicSpace P ⊤ hpb le_top hs⟩
    ¬ IsFiniteEtale (𝟙 X) ∧ ¬ IsEtaleLocalDescription (𝟙 X) := by
  intro P hpb X
  have hnotAn : ¬ X.IsAnalytic := by
    rw [isAnalytic_spa_iff P ⊤ hpb le_top hs]; intro heq
    have hmem : trivialSection (⊤ : PrimeSpectrum ℤ_[p]) ∈
        ValuationSpectrum.spa (⊤ : Subring ℤ_[p]) := by
      rw [spa_padicInt]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← heq, spaAnalytic_padicInt, Set.mem_singleton_iff] at hmem
    exact TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_ne_trivialSection_top hmem.symm
  exact ⟨mt isFiniteEtale_id_iff.mp hnotAn, mt isEtaleLocalDescription_id_iff.mp hnotAn⟩

/-- Morphisms from the empty adic space `Spa(0, 0)` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale,
étale, and not surjective on underlying points. -/
example :
    let S₁ := (Pair.powerBounded ℚ_[p]).polydisc 1
    let hS₁ := isSheafyForEveryPresentation_of_isStronglyNoetherian S₁.isRingOfIntegralElements
    ∃ E : AdicSpace.{0}, IsEmpty E.obj ∧ ∀ f : E ⟶ AdicSpace.ofPair S₁ hS₁,
      IsFiniteEtale f ∧ IsEtaleLocalDescription f ∧ ¬ Function.Surjective f.hom.base := by
  intro S₁ hS₁
  let _ : IsTateRing PUnit := IsTateRing.of_isModuleTopology (A := ℚ_[p]) (B := PUnit)
  have _ : IsStronglyNoetherian PUnit := IsNoetherianType.isStronglyNoetherian
  have hE : IsSheafyForEveryPresentation (Pair.discrete PUnit).plus :=
    isSheafyForEveryPresentation_of_isStronglyNoetherian
      (Pair.discrete PUnit).isRingOfIntegralElements
  have hempty : IsEmpty (AdicSpace.ofPair (Pair.discrete PUnit) hE).obj :=
    (AdicSpace.ofPairHomeomorph (Pair.discrete PUnit) hE).toEquiv.isEmpty_congr.mpr
      (Set.isEmpty_coe_sort.mpr
        ((spa_eq_empty_iff_subsingleton _ (Pair.discrete PUnit).isRingOfIntegralElements).mpr
          inferInstance))
  refine ⟨_, hempty, fun f ↦ ⟨.of_isEmpty f (IsAnalytic.ofPair _ _),
    .of_isEmpty f (IsAnalytic.ofPair _ _), fun hsurj ↦ ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ : (ValuationSpectrum.spa (Pair.powerBounded ℚ_[p]).plus).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h ↦ not_subsingleton ℚ_[p]
      ((spa_eq_empty_iff_subsingleton _ (Pair.powerBounded ℚ_[p]).isRingOfIntegralElements).mp h)
  rw [Pair.powerBounded_plus] at hx₀
  obtain ⟨e, _⟩ := hsurj ((AdicSpace.ofPairHomeomorph _ hS₁).symm
    ((Pair.polydisc.closedPolydiscHomeomorph 1).symm
      (classicalPoint ⟨x₀, hx₀⟩ 0 fun _ ↦ isPowerBounded_zero)))
  exact hempty.false e

/-- The open immersion of `{|T| ≤ |p|}` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is étale and not finite
étale. -/
example :
    let S₁ := (Pair.powerBounded ℚ_[p]).polydisc 1
    let hS₁ := isSheafyForEveryPresentation_of_isStronglyNoetherian S₁.isRingOfIntegralElements
    let D := AdicSpace.ofPair S₁ hS₁
    let e := (AdicSpace.ofPairHomeomorph _ hS₁).trans (Pair.polydisc.closedPolydiscHomeomorph 1)
    let U : Opens D.obj := ⟨e ⁻¹' closedSubdisc 0 (p : ℚ_[p]),
      (isOpen_closedSubdisc 0 (p : ℚ_[p])).preimage e.continuous⟩
    let j : (⟨D.obj.restrict U.isOpenEmbedding, isAdic_restrict _ D.property⟩ :
        AdicSpace.{0}) ⟶ D := ObjectProperty.homMk (D.obj.ofRestrict U.isOpenEmbedding)
    IsEtaleLocalDescription j ∧ ¬ IsFiniteEtale j := by
  intro S₁ hS₁ D e U j
  have _ : PreAdicSpace.IsOpenImmersion j.hom :=
    inferInstanceAs (PreAdicSpace.IsOpenImmersion (D.obj.ofRestrict U.isOpenEmbedding))
  refine ⟨.of_isOpenImmersion j (IsAnalytic.ofPair _ _), fun hj ↦ ?_⟩
  have hcl : IsClosed (U : Set D.obj) := by
    convert hj.isClopen_range.isClosed
    exact Set.ext fun x ↦ ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  have hp_pos : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (mod_cast (Fact.out : p.Prime).ne_zero)
  have hp_lt : ‖(p : ℚ_[p])‖ < 1 := _root_.Padic.norm_p_lt_one
  have hcl_sub : IsClosed (closedSubdisc 0 (p : ℚ_[p])) := by
    have hpre : e.symm ⁻¹' (U : Set D.obj) = closedSubdisc 0 (p : ℚ_[p]) := by ext; simp [U]
    exact hpre ▸ hcl.preimage e.symm.continuous
  have hmem : gaussPoint hp_pos hp_lt.le ∈ closedSubdisc 0 (p : ℚ_[p]) :=
    (gaussPoint_mem_closedSubdisc_iff hp_pos hp_lt.le 0 (p : ℚ_[p])).mpr
      ⟨by rw [norm_zero]; exact hp_pos.le, le_rfl⟩
  have hnotmem : gaussPointAbove hp_pos hp_lt ∉ closedSubdisc 0 (p : ℚ_[p]) := by
    rw [gaussPointAbove_mem_closedSubdisc_zero_iff]; exact lt_irrefl _
  exact hnotmem (hcl_sub.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    (specializes_iff_mem_closure.mp (gaussPoint_specializes_gaussPointAbove hp_pos hp_lt)))

/-- The diagonal Huber-pair morphism `D₁ → D₁.finiteAlgebra (A × A)` over `A = ℚ_[p]⟨T⟩` is finite
étale and induces a morphism of adic spaces that is both finite étale and étale. -/
example :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let D₁ := (Pair.powerBounded ℚ_[p]).polydisc 1
    let hD₁ := isSheafyForEveryPresentation_of_isStronglyNoetherian D₁.isRingOfIntegralElements
    let φ := Pair.finiteAlgebra.algebraHom D₁ (A × A)
    ∃ hB : IsSheafyForEveryPresentation (D₁.finiteAlgebra (A × A)).plus,
      φ.IsFiniteEtale ∧ IsFiniteEtale (AdicSpace.comapOfPair hD₁ hB φ) ∧
        IsEtaleLocalDescription (AdicSpace.comapOfPair hD₁ hB φ) := by
  intro A D₁ hD₁ φ
  have hφ : φ.IsFiniteEtale := Pair.finiteAlgebra.isFiniteEtale_algebraHom D₁ (A × A)
  have _ : IsStronglyNoetherian (A × A) :=
    hφ.isFinite.isTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom.isStronglyNoetherian
  have hB : IsSheafyForEveryPresentation (D₁.finiteAlgebra (A × A)).plus :=
    isSheafyForEveryPresentation_of_isStronglyNoetherian
      (D₁.finiteAlgebra (A × A)).isRingOfIntegralElements
  have hfe : IsFiniteEtale (AdicSpace.comapOfPair hD₁ hB φ) := .spa hD₁ hB φ hφ
  exact ⟨hB, hφ, hfe, .of_isFiniteEtale hfe⟩

/-- Neither the squaring morphism `Spa(ℚ_[p]⟨S⟩, ℤ_[p]⟨S⟩) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ S²`,
for any prime `p` including `p = 2`) nor the origin closed immersion
`Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ 0`) is étale or finite étale. -/
example :
    let S₀ := Pair.powerBounded ℚ_[p]
    let D₁ := S₀.polydisc 1
    let hS₀ := isSheafyForEveryPresentation_of_isStronglyNoetherian S₀.isRingOfIntegralElements
    let hD₁ := isSheafyForEveryPresentation_of_isStronglyNoetherian D₁.isRingOfIntegralElements
    let X := Pair.polydiscVar 1 ℚ_[p] 0
    let sqPair : Pair.Hom D₁ D₁ :=
      Pair.polydisc.evalHom (S₀.weightedCompletionHom isWeightFamily_one_weight)
        fun _ ↦ ⟨X ^ 2, Subring.pow_mem _ (S₀.polydiscVar_mem_polydiscPlus 1 0) 2⟩
    let originPair : Pair.Hom D₁ S₀ := Pair.polydisc.evalHom (Pair.Hom.id S₀) fun _ ↦ 0
    let sq := AdicSpace.comapOfPair hD₁ hD₁ sqPair
    let origin := AdicSpace.comapOfPair hD₁ hS₀ originPair
    (¬ IsEtaleLocalDescription sq ∧ ¬ IsFiniteEtale sq) ∧
      (¬ IsEtaleLocalDescription origin ∧ ¬ IsFiniteEtale origin) := by
  intro S₀ D₁ hS₀ hD₁ X sqPair originPair sq origin
  let I₀ : Ideal (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) := Ideal.span {X ^ 2}
  let D := restrictedMvPowerSeriesCompletion 1 ℚ_[p] ⧸ I₀
  let _ : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace D
  have _ : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace D := QuotientAddGroup.completeSpace_right _ I₀.toAddSubgroup
  have _ : IsTateRing D := .of_continuous (QuotientRing.isOpenQuotientMap_mk I₀).continuous
  have _ : IsStronglyNoetherian D :=
    IsStronglyNoetherian.quotient I₀ (IsNoetherianType.isClosed_ideal I₀)
  let dualPair : Pair D := D₁.quotient I₀
  have hD : IsSheafyForEveryPresentation dualPair.plus :=
    isSheafyForEveryPresentation_of_isStronglyNoetherian dualPair.isRingOfIntegralElements
  let ε : D := Ideal.Quotient.mk I₀ X
  have hε_plus : ε ∈ dualPair.plus := by
    simpa only [ε, Pair.Hom.toRingHom_quotientHom] using
      (D₁.quotientHom I₀).map_mem_plus X (S₀.polydiscVar_mem_polydiscPlus 1 0)
  have hε_sq : ε ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hε_ne : ε ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; rintro ⟨g, hg⟩
    let toPS : restrictedMvPowerSeriesCompletion 1 ℚ_[p] →+* PowerSeries ℚ_[p] :=
      (PowerSeries.IsRestricted.subring 1).subtype.comp
        restrictedMvPowerSeriesCompletionOneEquiv.toRingHom
    have hX : toPS X = PowerSeries.X := by simp [toPS, X, Pair.polydiscVar]
    have hps := congrArg (PowerSeries.coeff 1 ∘ toPS) hg
    simp only [Function.comp_apply, map_mul, hX, pow_two, mul_assoc] at hps
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul] at hps
    exact one_ne_zero hps
  let J : Ideal D := Ideal.span {ε}
  have hJ_sq : J ^ 2 = ⊥ := by rw [Ideal.span_singleton_pow, hε_sq, Ideal.span_singleton_eq_bot]
  have hεJ : Ideal.Quotient.mk J ε = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have _ : IsClosed (J : Set D) := IsNoetherianType.isClosed_ideal J
  have hQ : IsSheafyForEveryPresentation (dualPair.quotient J).plus := by
    let _ : UniformSpace (D ⧸ J) := IsTopologicalAddGroup.rightUniformSpace (D ⧸ J)
    have _ : IsUniformAddGroup (D ⧸ J) := isUniformAddGroup_of_addCommGroup
    have _ : CompleteSpace (D ⧸ J) := QuotientAddGroup.completeSpace_right _ J.toAddSubgroup
    have _ : IsTateRing (D ⧸ J) := .of_continuous (QuotientRing.isOpenQuotientMap_mk J).continuous
    have _ : IsStronglyNoetherian (D ⧸ J) := IsStronglyNoetherian.quotient J ‹_›
    exact isSheafyForEveryPresentation_of_isStronglyNoetherian
      (dualPair.quotient J).isRingOfIntegralElements
  let baseHom := (D₁.quotientHom I₀).comp (S₀.weightedCompletionHom isWeightFamily_one_weight)
  let σ₀ := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ (0 : dualPair.plus))
  let σ_ε := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ ⟨ε, hε_plus⟩)
  have hnot_sq : ¬ IsEtaleLocalDescription sq := fun hsq ↦ by
    let g₁ := AdicSpace.comapOfPair hD₁ hD σ₀
    let g₂ := AdicSpace.comapOfPair hD₁ hD σ_ε
    have hf_eq : g₁ ≫ sq = g₂ ≫ sq := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1
      refine Pair.polydisc.hom_ext (by simp [Pair.Hom.comp_assoc, sqPair, σ₀, σ_ε]) fun i ↦ ?_
      fin_cases i; simp [sqPair, σ₀, σ_ε, X, hε_sq]
    have hι_eq : AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ g₁ =
        AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ g₂ := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1
      refine Pair.polydisc.hom_ext (by simp [Pair.Hom.comp_assoc, σ₀, σ_ε]) fun i ↦ ?_
      fin_cases i
      simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, σ₀, σ_ε,
        Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero,
        Pair.Hom.toRingHom_quotientHom, hεJ]
    have hσ_eq : σ₀ = σ_ε := by
      simpa only [g₁, g₂, AdicSpace.ofPairHomEquiv_comapOfPair] using congrArg
        (AdicSpace.ofPairHomEquiv hD₁ hD)
        (hsq.eq_of_sqZero_quotient dualPair hD J hJ_sq hQ hf_eq hι_eq)
    have h0 := congrArg (fun φ : Pair.Hom _ _ ↦ φ.toRingHom X) hσ_eq
    simp only [σ₀, σ_ε, X, Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero] at h0
    exact hε_ne h0.symm
  have hnot_orig : ¬ IsEtaleLocalDescription origin := fun horig ↦ by
    let g₀Pair := (dualPair.quotientHom J).comp baseHom
    let g₀ := AdicSpace.comapOfPair hS₀ hQ g₀Pair
    let h := AdicSpace.comapOfPair hD₁ hD σ_ε
    have hcomm : g₀ ≫ origin = AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ h := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1
      refine Pair.polydisc.hom_ext (by simp [Pair.Hom.comp_assoc, originPair, σ_ε, g₀Pair]) fun i ↦
        ?_
      fin_cases i
      simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, originPair, σ_ε,
        Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero,
        Pair.Hom.toRingHom_quotientHom, hεJ]
    obtain ⟨g, _, hgf⟩ := horig.exists_of_sqZero_quotient dualPair hD J hJ_sq hQ g₀ h hcomm
    have hpair := congrArg (AdicSpace.ofPairHomEquiv hD₁ hD) hgf
    rw [AdicSpace.ofPairHomEquiv_comp, AdicSpace.ofPairHomEquiv_comapOfPair,
      AdicSpace.ofPairHomEquiv_comapOfPair] at hpair
    have h0 := congrArg (fun φ : Pair.Hom _ _ ↦ φ.toRingHom X) hpair
    simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, originPair, σ_ε, X,
      Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero] at h0
    exact hε_ne h0.symm
  exact ⟨⟨hnot_sq, fun h ↦ hnot_sq (.of_isFiniteEtale h)⟩,
    ⟨hnot_orig, fun h ↦ hnot_orig (.of_isFiniteEtale h)⟩⟩

end TauCeti.AdicSpace.Examples
