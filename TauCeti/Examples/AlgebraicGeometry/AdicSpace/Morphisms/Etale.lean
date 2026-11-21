/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Pair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc
public import TauCeti.RingTheory.Etale.Idempotent
public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.RingTheory.Huber.NoetherianType.Quotient
public import TauCeti.RingTheory.Huber.NoetherianType.Tate
public import TauCeti.RingTheory.Huber.Padic.TateAlgebra
public import TauCeti.RingTheory.Huber.Prod
public import TauCeti.RingTheory.Huber.Restricted.OneVariable

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

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology UniformSpace IsLocalRing

namespace TauCeti.AdicSpace.Examples

open Huber PreAdicSpace ValuationSpectrum

variable (p : ℕ) [Fact p.Prime]

/-- The `p`-adic base Huber pair `(ℚ_[p], ℤ_[p])`. -/
noncomputable abbrev basePair : Pair ℚ_[p] := Pair.powerBounded ℚ_[p]

/-- The closed unit disc Huber pair `(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` over `ℚ_[p]`. -/
noncomputable abbrev discPair := (basePair p).polydisc 1

/-- Sheafiness of `(ℚ_[p], ℤ_[p])`. -/
theorem isSheafy_basePair : IsSheafyForEveryPresentation (basePair p).plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian (basePair p).isRingOfIntegralElements

/-- Sheafiness of `(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)`. -/
theorem isSheafy_discPair : IsSheafyForEveryPresentation (discPair p).plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian (discPair p).isRingOfIntegralElements

/-- The identities on `Spa(ℚ_[p], ℤ_[p])` and `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale and
étale. -/
example :
    let X₀ := AdicSpace.ofPair (basePair p) (isSheafy_basePair p)
    let X₁ := AdicSpace.ofPair (discPair p) (isSheafy_discPair p)
    IsFiniteEtale (𝟙 X₀) ∧ IsEtaleLocalDescription (𝟙 X₀) ∧
      IsFiniteEtale (𝟙 X₁) ∧ IsEtaleLocalDescription (𝟙 X₁) :=
  ⟨.id (.ofPair _ _), .id (.ofPair _ _), .id (.ofPair _ _), .id (.ofPair _ _)⟩

/-- Conditional on sheafiness of its structure presheaf (`hs`), `Spa(ℤ_[p], ℤ_[p])` is not analytic,
so its identity is neither finite étale nor étale. -/
example :
    let P := PairOfDefinition.adic (maximalIdeal ℤ_[p]) PadicInt.isAdic_maximalIdeal
      (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _)
    let hpb : ∀ ⦃a : ℤ_[p]⦄, a ∈ (⊤ : Subring ℤ_[p]) → IsPowerBounded a :=
      fun a _ ↦ IsPowerBounded.of_norm_le_one (_root_.PadicInt.norm_le_one a)
    ∀ hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (⊤ : Subring ℤ_[p])))
      (presentationLimitPresheaf P (⊤ : Subring ℤ_[p])),
      let X : AdicSpace.{0} := ⟨presentationLimitPreAdicSpace P ⊤ hpb le_top,
        isAdic_presentationLimitPreAdicSpace P ⊤ hpb le_top hs⟩
      ¬ IsFiniteEtale (𝟙 X) ∧ ¬ IsEtaleLocalDescription (𝟙 X) := by
  intro P hpb hs X
  have hnotAn : ¬ X.IsAnalytic := by
    rw [isAnalytic_spa_iff P ⊤ hpb le_top hs]; intro heq
    have hmem : trivialSection (⊤ : PrimeSpectrum ℤ_[p]) ∈ spa (⊤ : Subring ℤ_[p]) := by
      rw [spa_padicInt]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← heq, spaAnalytic_padicInt, Set.mem_singleton_iff] at hmem
    exact TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_ne_trivialSection_top hmem.symm
  exact ⟨mt isFiniteEtale_id_iff.mp hnotAn, mt isEtaleLocalDescription_id_iff.mp hnotAn⟩

/-- Morphisms from the empty adic space `Spa(0, 0)` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale,
étale, and not surjective on underlying points. -/
example : ∃ E : AdicSpace.{0}, IsEmpty E.obj ∧
    ∀ f : E ⟶ AdicSpace.ofPair (discPair p) (isSheafy_discPair p),
      IsFiniteEtale f ∧ IsEtaleLocalDescription f ∧ ¬ Function.Surjective f.hom.base := by
  let _ : IsTateRing PUnit := IsTateRing.of_isModuleTopology (A := ℚ_[p]) (B := PUnit)
  have _ : IsStronglyNoetherian PUnit := IsNoetherianType.isStronglyNoetherian
  have hE := isSheafyForEveryPresentation_of_isStronglyNoetherian
    (Pair.discrete PUnit).isRingOfIntegralElements
  have hempty : IsEmpty (AdicSpace.ofPair (Pair.discrete PUnit) hE).obj :=
    (AdicSpace.ofPairHomeomorph _ hE).toEquiv.isEmpty_congr.mpr (Set.isEmpty_coe_sort.mpr
      ((spa_eq_empty_iff_subsingleton _ (Pair.discrete PUnit).isRingOfIntegralElements).mpr
        inferInstance))
  refine ⟨_, hempty, fun f ↦ ⟨.of_isEmpty f (.ofPair _ _), .of_isEmpty f (.ofPair _ _), fun h ↦ ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ : (spa (basePair p).plus).Nonempty :=
    Set.ne_empty_iff_nonempty.mp fun h ↦ not_subsingleton ℚ_[p]
      ((spa_eq_empty_iff_subsingleton _ (basePair p).isRingOfIntegralElements).mp h)
  rw [Pair.powerBounded_plus] at hx₀
  obtain ⟨e, _⟩ := h ((AdicSpace.ofPairHomeomorph _ (isSheafy_discPair p)).symm
    ((Pair.polydisc.closedPolydiscHomeomorph 1).symm
      (classicalPoint ⟨x₀, hx₀⟩ 0 fun _ ↦ isPowerBounded_zero)))
  exact hempty.false e

/-- The open immersion of `{|T| ≤ |p|}` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is étale and not finite
étale. -/
example :
    let D := AdicSpace.ofPair (discPair p) (isSheafy_discPair p)
    let e := (AdicSpace.ofPairHomeomorph _ (isSheafy_discPair p)).trans
      (Pair.polydisc.closedPolydiscHomeomorph 1)
    let U : Opens D.obj := ⟨e ⁻¹' closedSubdisc 0 (p : ℚ_[p]),
      (isOpen_closedSubdisc 0 (p : ℚ_[p])).preimage e.continuous⟩
    let j : (⟨D.obj.restrict U.isOpenEmbedding, isAdic_restrict _ D.property⟩ :
        AdicSpace.{0}) ⟶ D := ObjectProperty.homMk (D.obj.ofRestrict U.isOpenEmbedding)
    IsEtaleLocalDescription j ∧ ¬ IsFiniteEtale j := by
  intro D e U j
  refine ⟨.of_isOpenImmersion j (.ofPair _ _), fun hj ↦ ?_⟩
  have hcl : IsClosed (U : Set D.obj) := by
    convert hj.isClopen_range.isClosed; exact (Opens.set_range_inclusion' U).symm
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
    let φ := Pair.finiteAlgebra.algebraHom (discPair p) (A × A)
    ∃ hB : IsSheafyForEveryPresentation ((discPair p).finiteAlgebra (A × A)).plus,
      φ.IsFiniteEtale ∧ IsFiniteEtale (AdicSpace.comapOfPair (isSheafy_discPair p) hB φ) ∧
        IsEtaleLocalDescription (AdicSpace.comapOfPair (isSheafy_discPair p) hB φ) := by
  intro A φ
  have hφ : φ.IsFiniteEtale := Pair.finiteAlgebra.isFiniteEtale_algebraHom (discPair p) (A × A)
  have _ : IsStronglyNoetherian (A × A) :=
    hφ.isFinite.isTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom.isStronglyNoetherian
  have hB := isSheafyForEveryPresentation_of_isStronglyNoetherian
    ((discPair p).finiteAlgebra (A × A)).isRingOfIntegralElements
  exact ⟨hB, hφ, .comapOfPair _ hB φ hφ, .of_isFiniteEtale (.comapOfPair _ hB φ hφ)⟩

/-- Neither the squaring morphism `Spa(ℚ_[p]⟨S⟩, ℤ_[p]⟨S⟩) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ S²`,
for any prime `p` including `p = 2`) nor the origin closed immersion
`Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ 0`) is étale or finite étale. -/
example :
    let X := Pair.polydiscVar 1 ℚ_[p] 0
    let sqPair : Pair.Hom (discPair p) (discPair p) :=
      Pair.polydisc.evalHom ((basePair p).weightedCompletionHom isWeightFamily_one_weight)
        fun _ ↦ ⟨X ^ 2, Subring.pow_mem _ ((basePair p).polydiscVar_mem_polydiscPlus 1 0) 2⟩
    let originPair := Pair.polydisc.evalHom (Pair.Hom.id (basePair p)) fun _ : Fin 1 ↦ 0
    let sq := AdicSpace.comapOfPair (isSheafy_discPair p) (isSheafy_discPair p) sqPair
    let origin := AdicSpace.comapOfPair (isSheafy_discPair p) (isSheafy_basePair p) originPair
    (¬ IsEtaleLocalDescription sq ∧ ¬ IsFiniteEtale sq) ∧
      (¬ IsEtaleLocalDescription origin ∧ ¬ IsFiniteEtale origin) := by
  intro X sqPair originPair sq origin
  -- Build the sheafy dual-number pair `D = ℚ_[p]⟨X⟩ ⧸ (X²)` and its square-zero ideal `J = (ε)`
  let I₀ : Ideal (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) := Ideal.span {X ^ 2}
  have hI₀ := IsNoetherianType.isClosed_ideal I₀
  let D := restrictedMvPowerSeriesCompletion 1 ℚ_[p] ⧸ I₀
  let _ : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace D
  have _ : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace D := QuotientAddGroup.completeSpace_right _ I₀.toAddSubgroup
  have _ : IsTateRing D := .of_continuous (QuotientRing.isOpenQuotientMap_mk I₀).continuous
  have _ : IsStronglyNoetherian D := IsStronglyNoetherian.quotient I₀ hI₀
  let dualPair : Pair D := (discPair p).quotient I₀
  have hD := isSheafyForEveryPresentation_of_isStronglyNoetherian dualPair.isRingOfIntegralElements
  let ε : D := Ideal.Quotient.mk I₀ X
  have hε_plus : ε ∈ dualPair.plus := by
    simpa only [ε, Pair.Hom.toRingHom_quotientHom] using
      ((discPair p).quotientHom I₀).map_mem_plus X ((basePair p).polydiscVar_mem_polydiscPlus 1 0)
  have hε_sq : ε ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hε_ne : ε ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; rintro ⟨g, hg⟩
    let toPS : restrictedMvPowerSeriesCompletion 1 ℚ_[p] →+* PowerSeries ℚ_[p] :=
      (PowerSeries.IsRestricted.subring 1).subtype.comp
        restrictedMvPowerSeriesCompletionOneEquiv.toRingHom
    have htoPS_X : toPS X = PowerSeries.X := by
      simp [toPS, X, Pair.polydiscVar]
    have hps := congrArg (PowerSeries.coeff 1 ∘ toPS) hg
    simp only [Function.comp_apply, map_mul, htoPS_X, pow_two, mul_assoc] at hps
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul] at hps
    exact one_ne_zero hps
  let J : Ideal D := Ideal.span {ε}
  have hJ_sq : J ^ 2 = ⊥ := by rw [Ideal.span_singleton_pow, hε_sq, Ideal.span_singleton_eq_bot]
  have hεJ : (dualPair.quotientHom J).toRingHom ε = 0 := by
    rw [Pair.Hom.toRingHom_quotientHom, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hJ := IsNoetherianType.isClosed_ideal J
  have hQ := isSheafyForEveryPresentation_quotient_of_isStronglyNoetherian J hJ
    (dualPair.quotient J).isRingOfIntegralElements
  -- Obstruct `sq` via `eq_of_sqZero_quotient` on the two lifts `0` and `ε`
  let baseHom := ((discPair p).quotientHom I₀).comp
    ((basePair p).weightedCompletionHom isWeightFamily_one_weight)
  let σ₀ := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ (0 : dualPair.plus))
  let σ_ε := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ ⟨ε, hε_plus⟩)
  have hσ₀_base : σ₀.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
      baseHom := Pair.polydisc.evalHom_comp_weightedCompletionHom baseHom _
  have hσε_base : σ_ε.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
      baseHom := Pair.polydisc.evalHom_comp_weightedCompletionHom baseHom _
  have hσ₀_X : σ₀.toRingHom X = 0 :=
    (Pair.polydisc.toRingHom_evalHom_polydiscVar baseHom _ (0 : Fin 1)).trans
      (ZeroMemClass.coe_zero _)
  have hσε_X : σ_ε.toRingHom X = ε :=
    Pair.polydisc.toRingHom_evalHom_polydiscVar baseHom _ (0 : Fin 1)
  have hsq_base : sqPair.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
      (basePair p).weightedCompletionHom isWeightFamily_one_weight :=
    Pair.polydisc.evalHom_comp_weightedCompletionHom _ _
  have hsq_X : sqPair.toRingHom X = X ^ 2 :=
    Pair.polydisc.toRingHom_evalHom_polydiscVar _ _ (0 : Fin 1)
  have horigin_base :
      originPair.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
        Pair.Hom.id (basePair p) :=
    Pair.polydisc.evalHom_comp_weightedCompletionHom (Pair.Hom.id (basePair p)) _
  have horigin_X : originPair.toRingHom X = 0 :=
    (Pair.polydisc.toRingHom_evalHom_polydiscVar (Pair.Hom.id (basePair p)) _ (0 : Fin 1)).trans
      (ZeroMemClass.coe_zero _)
  have hcomp_origin_X (φ : Pair.Hom (basePair p) dualPair) :
      (φ.comp originPair).toRingHom X = 0 := by
    rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, horigin_X, map_zero]
  have hom_eq {C : Type} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
      [T0Space C] {T : Pair C} {φ₁ φ₂ : Pair.Hom (discPair p) T}
      (h0 : φ₁.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
        φ₂.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight))
      (hX : φ₁.toRingHom X = φ₂.toRingHom X) : φ₁ = φ₂ :=
    Pair.polydisc.hom_ext h0 fun i ↦ by fin_cases i; exact hX
  have hnot_sq : ¬ IsEtaleLocalDescription sq := fun hsq ↦ by
    let g₁ := AdicSpace.comapOfPair (isSheafy_discPair p) hD σ₀
    let g₂ := AdicSpace.comapOfPair (isSheafy_discPair p) hD σ_ε
    have hf_eq : g₁ ≫ sq = g₂ ≫ sq := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1; apply hom_eq
      · rw [Pair.Hom.comp_assoc, hsq_base, hσ₀_base, Pair.Hom.comp_assoc, hsq_base, hσε_base]
      · rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, hsq_X, map_pow, hσ₀_X,
          zero_pow two_ne_zero, Pair.Hom.toRingHom_comp, RingHom.comp_apply, hsq_X, map_pow,
          hσε_X, hε_sq]
    have hι_eq : AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ g₁ =
        AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ g₂ := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1; apply hom_eq
      · rw [Pair.Hom.comp_assoc, hσ₀_base, Pair.Hom.comp_assoc, hσε_base]
      · rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, hσ₀_X, map_zero,
          Pair.Hom.toRingHom_comp, RingHom.comp_apply, hσε_X]
        exact hεJ.symm
    have hσ_eq : σ₀ = σ_ε := by
      have h := congrArg (AdicSpace.ofPairHomEquiv (isSheafy_discPair p) hD)
        (hsq.eq_of_sqZero_quotient dualPair hD J hJ_sq hQ hf_eq hι_eq)
      rwa [AdicSpace.ofPairHomEquiv_comapOfPair, AdicSpace.ofPairHomEquiv_comapOfPair] at h
    have hX_eq := congrArg (Pair.Hom.toRingHom · X) hσ_eq.symm
    rw [hσε_X, hσ₀_X] at hX_eq
    exact hε_ne hX_eq
  -- Obstruct `origin` via `exists_of_sqZero_quotient` against `σ_ε`
  have hnot_orig : ¬ IsEtaleLocalDescription origin := fun horig ↦ by
    let g₀ := AdicSpace.comapOfPair (isSheafy_basePair p) hQ ((dualPair.quotientHom J).comp baseHom)
    let h := AdicSpace.comapOfPair (isSheafy_discPair p) hD σ_ε
    have hcomm : g₀ ≫ origin = AdicSpace.comapOfPair hD hQ (dualPair.quotientHom J) ≫ h := by
      rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]; congr 1; apply hom_eq
      · rw [Pair.Hom.comp_assoc, horigin_base, Pair.Hom.comp_id, Pair.Hom.comp_assoc, hσε_base]
      · rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, horigin_X, map_zero,
          Pair.Hom.toRingHom_comp, RingHom.comp_apply, hσε_X]
        exact hεJ.symm
    obtain ⟨g, _, hgf⟩ := horig.exists_of_sqZero_quotient dualPair hD J hJ_sq hQ g₀ h hcomm
    have hpair := congrArg (AdicSpace.ofPairHomEquiv (isSheafy_discPair p) hD) hgf
    rw [AdicSpace.ofPairHomEquiv_comp, AdicSpace.ofPairHomEquiv_comapOfPair,
      AdicSpace.ofPairHomEquiv_comapOfPair] at hpair
    have hX_eq := congrArg (Pair.Hom.toRingHom · X) hpair.symm
    rw [hσε_X, hcomp_origin_X] at hX_eq
    exact hε_ne hX_eq
  exact ⟨⟨hnot_sq, mt .of_isFiniteEtale hnot_sq⟩, ⟨hnot_orig, mt .of_isFiniteEtale hnot_orig⟩⟩

end TauCeti.AdicSpace.Examples
