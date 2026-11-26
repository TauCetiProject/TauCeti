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
  ⟨isFiniteEtale_id (.ofPair _ _), .id (.ofPair _ _), isFiniteEtale_id (.ofPair _ _),
    .id (.ofPair _ _)⟩

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
    let j := D.ofRestrict U
    IsEtaleLocalDescription j ∧ ¬ IsFiniteEtale j := by
  intro D e U j
  refine ⟨.of_isOpenImmersion j (.ofPair _ _), fun hj ↦ ?_⟩
  have hcl : IsClosed (U : Set D.obj) := by
    have hr : Set.range j.hom.base = (U : Set D.obj) := by
      rw [AdicSpace.ofRestrict_hom]
      exact Opens.set_range_inclusion' U
    exact hr ▸ hj.isClopen_range.isClosed
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
  exact ⟨hB, hφ, AdicSpace.isFiniteEtale_comapOfPair _ hB φ hφ,
    .of_isFiniteEtale (AdicSpace.isFiniteEtale_comapOfPair _ hB φ hφ)⟩

private structure DualNumberData (p : ℕ) [Fact p.Prime] : Type 1 where
  /-- Dual-number coefficient ring `ℚ_[p]⟨X⟩ ⧸ (X²)`. -/
  D : Type
  [commRing : CommRing D]
  [uniformSpace : UniformSpace D]
  [isUniformAddGroup : IsUniformAddGroup D]
  [isTopologicalRing : IsTopologicalRing D]
  [completeSpace : CompleteSpace D]
  [t0Space : T0Space D]
  [isHuberRing : IsHuberRing D]
  /-- Huber pair on `D` induced by the quotient of `discPair p` by `(X²)`. -/
  pair : Pair D
  /-- Sheafiness of `pair`. -/
  isSheafy : IsSheafyForEveryPresentation pair.plus
  /-- Dual-number generator `ε = X mod (X²)`. -/
  ε : D
  ε_mem_plus : ε ∈ pair.plus
  ε_sq : ε ^ 2 = 0
  ε_ne_zero : ε ≠ 0
  /-- Square-zero ideal `(ε)` in `D`. -/
  ideal : Ideal D
  ideal_sq : ideal ^ 2 = ⊥
  mk_ε : Ideal.Quotient.mk ideal ε = 0
  [t0SpaceQuotient : T0Space (D ⧸ ideal)]
  /-- Sheafiness of the quotient Huber pair `pair.quotient ideal`. -/
  isSheafyQuotient : IsSheafyForEveryPresentation (pair.quotient ideal).plus
  /-- Base Huber-pair morphism `(ℚ_[p], ℤ_[p]) → (D, D⁺)`. -/
  baseHom : Pair.Hom (basePair p) pair
  /-- Evaluation of `discPair p` at `T ↦ 0` in `dualPair`. -/
  σ₀ : Pair.Hom (discPair p) pair
  /-- Evaluation of `discPair p` at `T ↦ ε` in `dualPair`. -/
  σ_ε : Pair.Hom (discPair p) pair
  σ₀_base : σ₀.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) = baseHom
  σε_base : σ_ε.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) = baseHom
  σ₀_X : σ₀.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0) = 0
  σε_X : σ_ε.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0) = ε

attribute [instance] DualNumberData.commRing DualNumberData.uniformSpace
  DualNumberData.isUniformAddGroup DualNumberData.isTopologicalRing
  DualNumberData.completeSpace DualNumberData.t0Space DualNumberData.isHuberRing
  DualNumberData.t0SpaceQuotient

private noncomputable def dualNumberData (p : ℕ) [Fact p.Prime] : DualNumberData p := by
  let X := Pair.polydiscVar 1 ℚ_[p] 0
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
    have htoPS_X : toPS X = PowerSeries.X := by simp [toPS, X, Pair.polydiscVar]
    have hps := congrArg (PowerSeries.coeff 1 ∘ toPS) hg
    simp only [Function.comp_apply, map_mul, htoPS_X, pow_two, mul_assoc] at hps
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul] at hps
    exact one_ne_zero hps
  let J : Ideal D := Ideal.span {ε}
  have hJ_sq : J ^ 2 = ⊥ := by rw [Ideal.span_singleton_pow, hε_sq, Ideal.span_singleton_eq_bot]
  have hεJ : Ideal.Quotient.mk J ε = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hJ := IsNoetherianType.isClosed_ideal J
  have hQ := isSheafyForEveryPresentation_quotient_of_isStronglyNoetherian J hJ
    (dualPair.quotient J).isRingOfIntegralElements
  let baseHom := ((discPair p).quotientHom I₀).comp
    ((basePair p).weightedCompletionHom isWeightFamily_one_weight)
  let σ₀ := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ (0 : dualPair.plus))
  let σ_ε := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ ⟨ε, hε_plus⟩)
  exact {
    D := D
    pair := dualPair
    isSheafy := hD
    ε := ε
    ε_mem_plus := hε_plus
    ε_sq := hε_sq
    ε_ne_zero := hε_ne
    ideal := J
    ideal_sq := hJ_sq
    mk_ε := hεJ
    isSheafyQuotient := hQ
    baseHom := baseHom
    σ₀ := σ₀
    σ_ε := σ_ε
    σ₀_base := Pair.polydisc.evalHom_comp_weightedCompletionHom baseHom _
    σε_base := Pair.polydisc.evalHom_comp_weightedCompletionHom baseHom _
    σ₀_X := (Pair.polydisc.toRingHom_evalHom_polydiscVar baseHom _ (0 : Fin 1)).trans
      (ZeroMemClass.coe_zero _)
    σε_X := Pair.polydisc.toRingHom_evalHom_polydiscVar baseHom _ (0 : Fin 1) }

private theorem comapOfPair_disc_comp_eq {C₁ C₂ C₃ : Type} [CommRing C₁] [TopologicalSpace C₁]
    [IsTopologicalRing C₁] [IsHuberRing C₁] [CommRing C₂] [TopologicalSpace C₂]
    [IsTopologicalRing C₂] [IsHuberRing C₂] [CommRing C₃] [TopologicalSpace C₃]
    [IsTopologicalRing C₃] [IsHuberRing C₃] [T0Space C₃] {T₁ : Pair C₁} {T₂ : Pair C₂}
    {T₃ : Pair C₃} (hT₁ : IsSheafyForEveryPresentation T₁.plus)
    (hT₂ : IsSheafyForEveryPresentation T₂.plus)
    (hT₃ : IsSheafyForEveryPresentation T₃.plus)
    {φ₁ : Pair.Hom (discPair p) T₁} {ψ₁ : Pair.Hom T₁ T₃}
    {φ₂ : Pair.Hom (discPair p) T₂} {ψ₂ : Pair.Hom T₂ T₃}
    (h0 : ψ₁.comp (φ₁.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight)) =
      ψ₂.comp (φ₂.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight)))
    (hX : ψ₁.toRingHom (φ₁.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0)) =
      ψ₂.toRingHom (φ₂.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0))) :
    AdicSpace.comapOfPair hT₁ hT₃ ψ₁ ≫ AdicSpace.comapOfPair (isSheafy_discPair p) hT₁ φ₁ =
      AdicSpace.comapOfPair hT₂ hT₃ ψ₂ ≫ AdicSpace.comapOfPair (isSheafy_discPair p) hT₂ φ₂ := by
  rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]
  congr 1
  refine Pair.polydisc.hom_ext ?_ fun i ↦ by
    rw [Subsingleton.elim i 0]
    simpa only [Pair.Hom.toRingHom_comp, RingHom.comp_apply] using hX
  simpa only [Pair.Hom.comp_assoc] using h0

/-- The squaring morphism `Spa(ℚ_[p]⟨S⟩, ℤ_[p]⟨S⟩) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ S²`,
for any prime `p` including `p = 2`) is neither étale nor finite étale. -/
example :
    let X := Pair.polydiscVar 1 ℚ_[p] 0
    let sqPair : Pair.Hom (discPair p) (discPair p) :=
      Pair.polydisc.evalHom ((basePair p).weightedCompletionHom isWeightFamily_one_weight)
        fun _ ↦ ⟨X ^ 2, Subring.pow_mem _ ((basePair p).polydiscVar_mem_polydiscPlus 1 0) 2⟩
    let sq := AdicSpace.comapOfPair (isSheafy_discPair p) (isSheafy_discPair p) sqPair
    ¬ IsEtaleLocalDescription sq ∧ ¬ IsFiniteEtale sq := by
  intro X sqPair sq
  let d := dualNumberData p
  have hsq_base : sqPair.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
      (basePair p).weightedCompletionHom isWeightFamily_one_weight :=
    Pair.polydisc.evalHom_comp_weightedCompletionHom _ _
  have hsq_X : sqPair.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0) = (Pair.polydiscVar 1 ℚ_[p] 0) ^ 2 :=
    Pair.polydisc.toRingHom_evalHom_polydiscVar _ _ (0 : Fin 1)
  have hnot : ¬ IsEtaleLocalDescription sq := fun hsq ↦ by
    let g₁ := AdicSpace.comapOfPair (isSheafy_discPair p) d.isSheafy d.σ₀
    let g₂ := AdicSpace.comapOfPair (isSheafy_discPair p) d.isSheafy d.σ_ε
    have hf_eq : g₁ ≫ sq = g₂ ≫ sq :=
      comapOfPair_disc_comp_eq p _ _ _ (by simp only [hsq_base, d.σ₀_base, d.σε_base])
        (by simp [hsq_X, d.σ₀_X, d.σε_X, d.ε_sq])
    have hι_eq : AdicSpace.comapOfPair d.isSheafy d.isSheafyQuotient
          (d.pair.quotientHom d.ideal) ≫ g₁ =
        AdicSpace.comapOfPair d.isSheafy d.isSheafyQuotient
          (d.pair.quotientHom d.ideal) ≫ g₂ :=
      comapOfPair_disc_comp_eq p _ _ _ (by simp only [d.σ₀_base, d.σε_base])
        (by simp [d.σ₀_X, d.σε_X, d.mk_ε])
    have hσ_eq : d.σ₀ = d.σ_ε := by
      simpa only [g₁, g₂, AdicSpace.ofPairHomEquiv_comapOfPair] using
        congrArg (AdicSpace.ofPairHomEquiv (isSheafy_discPair p) d.isSheafy)
          (hsq.eq_of_sqZero_quotient d.pair d.isSheafy d.ideal d.ideal_sq d.isSheafyQuotient
            hf_eq hι_eq)
    have hX_eq := congrArg (Pair.Hom.toRingHom · (Pair.polydiscVar 1 ℚ_[p] 0)) hσ_eq.symm
    rw [d.σε_X, d.σ₀_X] at hX_eq
    exact d.ε_ne_zero hX_eq
  exact ⟨hnot, mt .of_isFiniteEtale hnot⟩

/-- The origin closed immersion `Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ 0`) is
neither étale nor finite étale. -/
example :
    let originPair := Pair.polydisc.evalHom (Pair.Hom.id (basePair p)) fun _ : Fin 1 ↦ 0
    let origin := AdicSpace.comapOfPair (isSheafy_discPair p) (isSheafy_basePair p) originPair
    ¬ IsEtaleLocalDescription origin ∧ ¬ IsFiniteEtale origin := by
  intro originPair origin
  let d := dualNumberData p
  have horigin_base :
      originPair.comp ((basePair p).weightedCompletionHom isWeightFamily_one_weight) =
        Pair.Hom.id (basePair p) :=
    Pair.polydisc.evalHom_comp_weightedCompletionHom (Pair.Hom.id (basePair p)) _
  have horigin_X : originPair.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0) = 0 :=
    (Pair.polydisc.toRingHom_evalHom_polydiscVar (Pair.Hom.id (basePair p)) _ (0 : Fin 1)).trans
      (ZeroMemClass.coe_zero _)
  have hnot : ¬ IsEtaleLocalDescription origin := fun horig ↦ by
    let g₀ := AdicSpace.comapOfPair (isSheafy_basePair p) d.isSheafyQuotient
      ((d.pair.quotientHom d.ideal).comp d.baseHom)
    let h := AdicSpace.comapOfPair (isSheafy_discPair p) d.isSheafy d.σ_ε
    have hcomm : g₀ ≫ origin =
        AdicSpace.comapOfPair d.isSheafy d.isSheafyQuotient (d.pair.quotientHom d.ideal) ≫ h :=
      comapOfPair_disc_comp_eq p _ _ _ (by simp only [horigin_base, d.σε_base, Pair.Hom.comp_id])
        (by simp [horigin_X, d.σε_X, d.mk_ε])
    obtain ⟨g, _, hgf⟩ := horig.exists_of_sqZero_quotient d.pair d.isSheafy d.ideal d.ideal_sq
      d.isSheafyQuotient g₀ h hcomm
    have hpair := congrArg (AdicSpace.ofPairHomEquiv (isSheafy_discPair p) d.isSheafy) hgf
    dsimp only [origin, h] at hpair
    simp only [AdicSpace.ofPairHomEquiv_comp, AdicSpace.ofPairHomEquiv_comapOfPair] at hpair
    have hX_eq := congrArg (Pair.Hom.toRingHom · (Pair.polydiscVar 1 ℚ_[p] 0)) hpair.symm
    simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, d.σε_X, horigin_X, map_zero] at hX_eq
    exact d.ε_ne_zero hX_eq
  exact ⟨hnot, mt .of_isFiniteEtale hnot⟩

end TauCeti.AdicSpace.Examples
