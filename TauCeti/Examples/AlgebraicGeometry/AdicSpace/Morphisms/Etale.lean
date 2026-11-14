/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Pair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc
public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.RingTheory.Huber.Padic.TateAlgebra

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.NoetherianType.Tate
import TauCeti.RingTheory.Huber.Restricted.OneVariable

/-!
# Examples of finite étale and étale morphisms of analytic adic spaces

Concrete positive and negative examples for `TauCeti.AdicSpace.IsFiniteEtale` and
`TauCeti.AdicSpace.IsEtaleLocalDescription` over `ℚ_[p]`:

* the identities on `Spa(ℚ_[p], ℤ_[p])` and `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale and étale,
  whereas the identity on the non-analytic space `Spa(ℤ_[p], ℤ_[p])` is neither;
* any morphism from the empty adic space `Spa(0, 0)` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is finite
  étale and étale, and is not surjective;
* the rational open immersion of the closed subdisc `{|T| ≤ |p|}` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)`
  satisfies `IsEtaleLocalDescription` (`of_isOpenImmersion`) and is not `IsFiniteEtale` (its image
  contains the radius-`|p|` Gauss point `η_{|p|}` without its specialization `η_{|p|⁺}`,
  contradicting `IsFiniteEtale.isClopen_range`);
* the trivial double cover `Spa(A × A, (A × A)°) ⟶ Spa(A, A°)` of the closed unit disc over `ℚ_[p]`
  is finite étale and étale;
* the squaring map `Spa(ℚ_[p]⟨S⟩, ℤ_[p]⟨S⟩) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` sending `T ↦ S²` is neither
  étale nor finite étale for any prime `p` (including `p = 2`), obstructed by failure of uniqueness
  in `IsEtaleLocalDescription.eq_of_sqZero_quotient` against `ℚ_[p]⟨X⟩ ⧸ (X²)`;
* the origin closed immersion `Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` at `T = 0` is neither
  étale nor finite étale, obstructed by failure of existence in
  `IsEtaleLocalDescription.exists_of_sqZero_quotient` against `ℚ_[p]⟨X⟩ ⧸ (X²)`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology UniformSpace IsLocalRing

namespace TauCeti.AdicSpace.Examples

open Huber PreAdicSpace ValuationSpectrum

section Helpers

variable (p : ℕ) [Fact p.Prime]

/-- The Huber pair `(ℚ_[p], ℤ_[p])` for a prime `p`. -/
noncomputable abbrev padicPair : Pair ℚ_[p] :=
  Pair.powerBounded ℚ_[p]

/-- `(ℚ_[p], ℤ_[p])` is sheafy for every presentation. -/
theorem isSheafy_padicPair : IsSheafyForEveryPresentation (padicPair p).plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian (padicPair p).isRingOfIntegralElements

/-- The Huber pair `(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` of the one-variable closed unit disc over `ℚ_[p]`. -/
noncomputable abbrev padicDiscPair : Pair (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) :=
  (padicPair p).polydisc 1

/-- `(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is sheafy for every presentation. -/
theorem isSheafy_padicDiscPair : IsSheafyForEveryPresentation (padicDiscPair p).plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian (padicDiscPair p).isRingOfIntegralElements

private theorem isAnalytic_ofPair_padic :
    (AdicSpace.ofPair (padicPair p) (isSheafy_padicPair p)).IsAnalytic := by
  let P := (isSheafy_padicPair p).exists_compatible_isSheaf.choose
  have hP := (isSheafy_padicPair p).exists_compatible_isSheaf.choose_spec.1
  exact (IsLocallyNoetherianAnalytic.spa P (padicPair p).plus
    (padicPair p).isRingOfIntegralElements.isPowerBounded_of_mem hP).isAnalytic.of_iso
    (AdicSpace.ofPairIsoOfPresentation (padicPair p) (isSheafy_padicPair p) P hP)

private theorem isAnalytic_ofPair_padicDisc :
    (AdicSpace.ofPair (padicDiscPair p) (isSheafy_padicDiscPair p)).IsAnalytic := by
  let P := (isSheafy_padicDiscPair p).exists_compatible_isSheaf.choose
  have hP := (isSheafy_padicDiscPair p).exists_compatible_isSheaf.choose_spec.1
  exact (IsLocallyNoetherianAnalytic.spa P (padicDiscPair p).plus
    (padicDiscPair p).isRingOfIntegralElements.isPowerBounded_of_mem hP).isAnalytic.of_iso
    (AdicSpace.ofPairIsoOfPresentation (padicDiscPair p) (isSheafy_padicDiscPair p) P hP)

private theorem nonempty_spa_padicPair : (ValuationSpectrum.spa (padicPair p).plus).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne,
    spa_eq_empty_iff_subsingleton _ (padicPair p).isRingOfIntegralElements]
  exact not_subsingleton ℚ_[p]

end Helpers

/-! ### Identities, non-analytic base control, and empty covers -/

section IdentitiesAndEmpty

variable (p : ℕ) [Fact p.Prime]

/-- The identities on `Spa(ℚ_[p], ℤ_[p])` and `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale and
étale. -/
example :
    let X₀ := AdicSpace.ofPair (padicPair p) (isSheafy_padicPair p)
    let X₁ := AdicSpace.ofPair (padicDiscPair p) (isSheafy_padicDiscPair p)
    IsFiniteEtale (𝟙 X₀) ∧ IsEtaleLocalDescription (𝟙 X₀) ∧
      IsFiniteEtale (𝟙 X₁) ∧ IsEtaleLocalDescription (𝟙 X₁) :=
  ⟨.id (isAnalytic_ofPair_padic p), .id (isAnalytic_ofPair_padic p),
    .id (isAnalytic_ofPair_padicDisc p), .id (isAnalytic_ofPair_padicDisc p)⟩

/-- `Spa(ℤ_[p], ℤ_[p])` is not analytic, so its identity is neither finite étale nor étale. -/
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
    let X : AdicSpace.{0} :=
      ⟨presentationLimitPreAdicSpace P ⊤ hpb le_top,
        isAdic_presentationLimitPreAdicSpace P ⊤ hpb le_top hs⟩
    ¬ IsFiniteEtale (𝟙 X) ∧ ¬ IsEtaleLocalDescription (𝟙 X) := by
  intro P hpb X
  have hnotAn : ¬ X.IsAnalytic := by
    rw [isAnalytic_spa_iff P ⊤ hpb le_top hs]
    intro heq
    have hmem : trivialSection (⊤ : PrimeSpectrum ℤ_[p]) ∈
        ValuationSpectrum.spa (⊤ : Subring ℤ_[p]) := by
      rw [spa_padicInt]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← heq, spaAnalytic_padicInt, Set.mem_singleton_iff] at hmem
    exact TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_ne_trivialSection_top hmem.symm
  exact ⟨mt isFiniteEtale_id_iff.mp hnotAn, mt isEtaleLocalDescription_id_iff.mp hnotAn⟩

/-- Morphisms from the empty adic space `Spa(0, 0)` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` are finite étale
and étale, and are not surjective on underlying points. -/
example :
    ∃ (E : AdicSpace.{0}), IsEmpty E.obj ∧
      ∀ f : E ⟶ AdicSpace.ofPair (padicDiscPair p) (isSheafy_padicDiscPair p),
        IsFiniteEtale f ∧ IsEtaleLocalDescription f ∧ ¬ Function.Surjective f.hom.base := by
  have hpu : IsPseudoUniformizer (0 : PUnit) :=
    isPseudoUniformizer_iff.mpr ⟨Subsingleton.elim (0 : PUnit) 1 ▸ isUnit_one, .zero⟩
  let _ : IsTateRing PUnit :=
    have _ : IsHuberRing PUnit := inferInstance
    ⟨⟨0, hpu⟩⟩
  have _ : IsStronglyNoetherian PUnit := IsNoetherianType.isStronglyNoetherian
  have hE_sheaf : IsSheafyForEveryPresentation (Pair.discrete PUnit).plus :=
    isSheafyForEveryPresentation_of_isStronglyNoetherian
      (Pair.discrete PUnit).isRingOfIntegralElements
  let E := AdicSpace.ofPair (Pair.discrete PUnit) hE_sheaf
  have hspa : ValuationSpectrum.spa (Pair.discrete PUnit).plus = ∅ :=
    (spa_eq_empty_iff_subsingleton _ (Pair.discrete PUnit).isRingOfIntegralElements).mpr
      inferInstance
  have hempty : IsEmpty E.obj :=
    (AdicSpace.ofPairHomeomorph (Pair.discrete PUnit) hE_sheaf).toEquiv.isEmpty_congr.mpr
      (Set.isEmpty_coe_sort.mpr hspa)
  refine ⟨E, hempty, fun f ↦ ⟨.of_isEmpty f (isAnalytic_ofPair_padicDisc p),
    .of_isEmpty f (isAnalytic_ofPair_padicDisc p), fun hsurj ↦ ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := nonempty_spa_padicPair p
  rw [Pair.powerBounded_plus] at hx₀
  let y₀ := (AdicSpace.ofPairHomeomorph _ (isSheafy_padicDiscPair p)).symm
    ((Pair.polydisc.closedPolydiscHomeomorph 1).symm
      (classicalPoint ⟨x₀, hx₀⟩ 0 fun _ ↦ isPowerBounded_zero))
  obtain ⟨e, _⟩ := hsurj y₀
  exact hempty.false e

end IdentitiesAndEmpty

/-! ### Separating étale from finite étale: rational subdisc inclusion -/

section SubdiscOpenImmersion

variable (p : ℕ) [Fact p.Prime]

/-- The open immersion of the rational subdisc `{|T| ≤ |p|}` into `Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` is
étale (`of_isOpenImmersion`) and not finite étale (`η_{|p|} ⤳ η_{|p|⁺}` witnesses non-closed
range). -/
example :
    let D := AdicSpace.ofPair (padicDiscPair p) (isSheafy_padicDiscPair p)
    let e := (AdicSpace.ofPairHomeomorph _ (isSheafy_padicDiscPair p)).trans
      (Pair.polydisc.closedPolydiscHomeomorph 1)
    let U : Opens D.obj :=
      ⟨e ⁻¹' closedSubdisc 0 (p : ℚ_[p]),
        (isOpen_closedSubdisc 0 (p : ℚ_[p])).preimage e.continuous⟩
    let D_sub : AdicSpace.{0} := ⟨D.obj.restrict U.isOpenEmbedding, isAdic_restrict _ D.property⟩
    let j : D_sub ⟶ D := ObjectProperty.homMk (D.obj.ofRestrict U.isOpenEmbedding)
    IsEtaleLocalDescription j ∧ ¬ IsFiniteEtale j := by
  intro D e U D_sub j
  have _ : PreAdicSpace.IsOpenImmersion j.hom :=
    inferInstanceAs (PreAdicSpace.IsOpenImmersion (D.obj.ofRestrict U.isOpenEmbedding))
  refine ⟨.of_isOpenImmersion j (isAnalytic_ofPair_padicDisc p), fun hj ↦ ?_⟩
  have hcl : IsClosed (U : Set D.obj) := by
    convert hj.isClopen_range.isClosed
    ext x
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  have hp_pos : 0 < ‖(p : ℚ_[p])‖ :=
    norm_pos_iff.mpr (mod_cast (Fact.out : p.Prime).ne_zero)
  have hp_lt : ‖(p : ℚ_[p])‖ < 1 := _root_.Padic.norm_p_lt_one
  have hcl_sub : IsClosed (closedSubdisc 0 (p : ℚ_[p])) := by
    have hpre : e.symm ⁻¹' (U : Set D.obj) = closedSubdisc 0 (p : ℚ_[p]) := by
      ext x
      simp [U]
    rw [← hpre]
    exact hcl.preimage e.symm.continuous
  have hmem : gaussPoint hp_pos hp_lt.le ∈ closedSubdisc 0 (p : ℚ_[p]) :=
    (gaussPoint_mem_closedSubdisc_iff hp_pos hp_lt.le 0 (p : ℚ_[p])).mpr
      ⟨by rw [norm_zero]; exact hp_pos.le, le_rfl⟩
  have hnotmem : gaussPointAbove hp_pos hp_lt ∉ closedSubdisc 0 (p : ℚ_[p]) := by
    rw [gaussPointAbove_mem_closedSubdisc_zero_iff]
    exact lt_irrefl _
  exact hnotmem (hcl_sub.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    (specializes_iff_mem_closure.mp (gaussPoint_specializes_gaussPointAbove hp_pos hp_lt)))

end SubdiscOpenImmersion

/-! ### Trivial double cover of the closed unit disc -/

section TrivialDoubleCover

variable (p : ℕ) [Fact p.Prime]

/-- The diagonal Huber-pair morphism `D₁ → D₁.finiteAlgebra (A × A)` over `A = ℚ_[p]⟨T⟩` is finite
étale and induces a morphism of adic spaces that is both finite étale and étale. -/
example :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let _ : IsHuberRing (A × A) :=
      (IsTateRing.of_isModuleTopology (A := A) (B := A × A)).toIsHuberRing
    let φ := Pair.finiteAlgebra.algebraHom (padicDiscPair p) (A × A)
    ∃ hB : IsSheafyForEveryPresentation ((padicDiscPair p).finiteAlgebra (A × A)).plus,
      φ.IsFiniteEtale ∧
        IsFiniteEtale (AdicSpace.comapOfPair (isSheafy_padicDiscPair p) hB φ) ∧
        IsEtaleLocalDescription (AdicSpace.comapOfPair (isSheafy_padicDiscPair p) hB φ) := by
  intro A _ φ
  have hφ : φ.IsFiniteEtale := Pair.finiteAlgebra.isFiniteEtale_algebraHom (padicDiscPair p) (A × A)
  have hft : IsTopologicallyFiniteType φ.toRingHom :=
    hφ.isFinite.isTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom
  have _ : IsTateRing (A × A) := IsTateRing.of_isModuleTopology (A := A) (B := A × A)
  have _ : IsStronglyNoetherian (A × A) := hft.isStronglyNoetherian
  have hB : IsSheafyForEveryPresentation ((padicDiscPair p).finiteAlgebra (A × A)).plus :=
    isSheafyForEveryPresentation_of_isStronglyNoetherian
      ((padicDiscPair p).finiteAlgebra (A × A)).isRingOfIntegralElements
  have hfe : IsFiniteEtale (AdicSpace.comapOfPair (isSheafy_padicDiscPair p) hB φ) :=
    .spa (isSheafy_padicDiscPair p) hB φ hφ
  exact ⟨hB, hφ, hfe, .of_isFiniteEtale hfe⟩

end TrivialDoubleCover

/-! ### Ramified squaring and unramified closed immersion via infinitesimal lifting -/

section InfinitesimalObstructions

variable (p : ℕ) [Fact p.Prime]

private noncomputable abbrev sqZeroIdeal : Ideal (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) :=
  Ideal.span {Pair.polydiscVar 1 ℚ_[p] 0 ^ 2}

private noncomputable abbrev dualNumbers : Type :=
  restrictedMvPowerSeriesCompletion 1 ℚ_[p] ⧸ sqZeroIdeal p

private noncomputable abbrev dualPair : Pair (dualNumbers p) :=
  (padicDiscPair p).quotient (sqZeroIdeal p)

private noncomputable abbrev dualEps : dualNumbers p :=
  Ideal.Quotient.mk (sqZeroIdeal p) (Pair.polydiscVar 1 ℚ_[p] 0)

private theorem dualEps_mem_plus : dualEps p ∈ (dualPair p).plus := by
  rw [dualEps, ← Pair.Hom.toRingHom_quotientHom (padicDiscPair p) (sqZeroIdeal p)]
  exact ((padicDiscPair p).quotientHom (sqZeroIdeal p)).map_mem_plus _
    ((padicPair p).polydiscVar_mem_polydiscPlus 1 0)

private theorem dualEps_sq : dualEps p ^ 2 = 0 := by
  rw [dualEps, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

private theorem dualEps_ne_zero : dualEps p ≠ 0 := by
  rw [dualEps, Ne, Ideal.Quotient.eq_zero_iff_mem, sqZeroIdeal, Ideal.mem_span_singleton]
  rintro ⟨g, hg⟩
  let toPS : restrictedMvPowerSeriesCompletion 1 ℚ_[p] →+* PowerSeries ℚ_[p] :=
    (PowerSeries.IsRestricted.subring 1).subtype.comp
      restrictedMvPowerSeriesCompletionOneEquiv.toRingHom
  have hX : toPS (Pair.polydiscVar 1 ℚ_[p] 0) = PowerSeries.X := by
    simp [toPS, Pair.polydiscVar]
  have hps := congrArg (PowerSeries.coeff 1 ∘ toPS) hg
  simp only [Function.comp_apply, map_mul, hX, sq, mul_assoc] at hps
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul] at hps
  exact one_ne_zero hps

private noncomputable abbrev dualNilIdeal : Ideal (dualNumbers p) :=
  Ideal.span {dualEps p}

private theorem dualNilIdeal_sq : dualNilIdeal p ^ 2 = ⊥ := by
  rw [dualNilIdeal, Ideal.span_singleton_pow, dualEps_sq, Ideal.span_singleton_eq_bot]

private theorem isStronglyNoetherian_dualNumbers : IsStronglyNoetherian (dualNumbers p) :=
  IsStronglyNoetherian.quotient (sqZeroIdeal p) (IsNoetherianType.isClosed_ideal (sqZeroIdeal p))

private theorem isClosed_dualNilIdeal : IsClosed (dualNilIdeal p : Set (dualNumbers p)) := by
  let _ : UniformSpace (dualNumbers p) := IsTopologicalAddGroup.rightUniformSpace (dualNumbers p)
  have _ : IsUniformAddGroup (dualNumbers p) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (dualNumbers p) :=
    QuotientAddGroup.completeSpace_right _ (sqZeroIdeal p).toAddSubgroup
  have _ : T2Space (dualNumbers p) := IsNoetherianType.t2Space_quotient (sqZeroIdeal p)
  have _ : IsTateRing (dualNumbers p) :=
    .of_continuous (QuotientRing.isOpenQuotientMap_mk (sqZeroIdeal p)).continuous
  have _ : IsStronglyNoetherian (dualNumbers p) := isStronglyNoetherian_dualNumbers p
  exact IsNoetherianType.isClosed_ideal (dualNilIdeal p)

private theorem isSheafy_dualPair : IsSheafyForEveryPresentation (dualPair p).plus := by
  let _ : UniformSpace (dualNumbers p) := IsTopologicalAddGroup.rightUniformSpace (dualNumbers p)
  have _ : IsUniformAddGroup (dualNumbers p) := isUniformAddGroup_of_addCommGroup
  have _ : IsTateRing (dualNumbers p) :=
    .of_continuous (QuotientRing.isOpenQuotientMap_mk (sqZeroIdeal p)).continuous
  have _ : IsStronglyNoetherian (dualNumbers p) := isStronglyNoetherian_dualNumbers p
  exact isSheafyForEveryPresentation_of_isStronglyNoetherian (dualPair p).isRingOfIntegralElements

private theorem isSheafy_dualQuotient :
    IsSheafyForEveryPresentation ((dualPair p).quotient (dualNilIdeal p)).plus := by
  let _ : UniformSpace (dualNumbers p) := IsTopologicalAddGroup.rightUniformSpace (dualNumbers p)
  have _ : IsUniformAddGroup (dualNumbers p) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (dualNumbers p) :=
    QuotientAddGroup.completeSpace_right _ (sqZeroIdeal p).toAddSubgroup
  have _ : T2Space (dualNumbers p) := IsNoetherianType.t2Space_quotient (sqZeroIdeal p)
  have _ : IsTateRing (dualNumbers p) :=
    .of_continuous (QuotientRing.isOpenQuotientMap_mk (sqZeroIdeal p)).continuous
  have _ : IsStronglyNoetherian (dualNumbers p) := isStronglyNoetherian_dualNumbers p
  let Q := dualNumbers p ⧸ dualNilIdeal p
  let _ : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have _ : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have _ : IsTateRing Q :=
    .of_continuous (QuotientRing.isOpenQuotientMap_mk (dualNilIdeal p)).continuous
  have _ : IsStronglyNoetherian Q :=
    IsStronglyNoetherian.quotient (dualNilIdeal p) (isClosed_dualNilIdeal p)
  exact isSheafyForEveryPresentation_of_isStronglyNoetherian
    ((dualPair p).quotient (dualNilIdeal p)).isRingOfIntegralElements

private theorem subsingleton_ofPair_dualPair :
    Subsingleton (AdicSpace.ofPair (dualPair p) (isSheafy_dualPair p)).obj := by
  suffices Subsingleton (ValuationSpectrum.spa (dualPair p).plus) from
    (AdicSpace.ofPairHomeomorph (dualPair p) (isSheafy_dualPair p)).injective.subsingleton
  obtain ⟨x₀, hx₀⟩ := nonempty_spa_padicPair p
  rw [Pair.powerBounded_plus] at hx₀
  let q := Pair.quotientHom (padicDiscPair p) (sqZeroIdeal p)
  let e := Pair.polydisc.closedPolydiscHomeomorph (K := ℚ_[p]) 1
  have hconst : ∀ w : ValuationSpectrum.spa (dualPair p).plus,
      e (q.spaComap w) = classicalPoint ⟨x₀, hx₀⟩ 0 fun _ ↦ isPowerBounded_zero := by
    intro w
    apply eq_classicalPoint_of_weightedX_sub_weightedC_mem_supp
    simp only [Pi.zero_apply, map_zero, sub_zero]
    refine (inferInstance : (e (q.spaComap w)).1.supp.IsPrime).mem_of_pow_mem 2 ?_
    have h1 : ((e (q.spaComap w)).1 : Spv _) =
        ValuationSpectrum.comap (q.toRingHom.comp Completion.coeRingHom) w.1 := by
      rw [Pair.polydisc.coe_closedPolydiscHomeomorph_apply, Pair.Hom.spaComap_val,
        ValuationSpectrum.comap_comp]
      rfl
    rw [h1, mem_supp_iff, comap_vle, RingHom.comp_apply, map_pow, map_zero,
      Pair.Hom.toRingHom_quotientHom, show Completion.coeRingHom _ = Pair.polydiscVar 1 ℚ_[p] 0
      from rfl, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)]
    exact w.1.toValuativeRel.vle_refl 0
  refine ⟨fun w₁ w₂ ↦ (Pair.Hom.isClosedEmbedding_spaComap_quotientHom _ _).injective
    (e.injective ((hconst w₁).trans (hconst w₂).symm))⟩

private theorem t0Space_dualNumbers : T0Space (dualNumbers p) :=
  @T1Space.t0Space _ _
    ((Ideal.Quotient.t1Space_iff _).mpr (IsNoetherianType.isClosed_ideal (sqZeroIdeal p)))

private theorem t0Space_dualQuotient : T0Space (dualNumbers p ⧸ dualNilIdeal p) :=
  @T1Space.t0Space _ _ ((Ideal.Quotient.t1Space_iff _).mpr (isClosed_dualNilIdeal p))

private noncomputable def dualReducedToPadicHom :
    Pair.Hom ((dualPair p).quotient (dualNilIdeal p)) (padicPair p) := by
  let ev₀ : Pair.Hom (padicDiscPair p) (padicPair p) :=
    Pair.polydisc.evalHom (Pair.Hom.id (padicPair p)) fun _ ↦ 0
  have hev₁ : sqZeroIdeal p ≤ RingHom.ker ev₀.toRingHom := by
    rw [sqZeroIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simp [ev₀]
  let π₁ := ev₀.quotientLift (sqZeroIdeal p) hev₁
  have hπ₁ : dualNilIdeal p ≤ RingHom.ker π₁.toRingHom := by
    rw [dualNilIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      show dualEps p = Ideal.Quotient.mk (sqZeroIdeal p) (Pair.polydiscVar 1 ℚ_[p] 0) from rfl]
    simp [π₁, ev₀]
  exact π₁.quotientLift (dualNilIdeal p) hπ₁

private noncomputable def dualReducedPoint :
    (AdicSpace.ofPair ((dualPair p).quotient (dualNilIdeal p)) (isSheafy_dualQuotient p)).obj :=
  (AdicSpace.ofPairHomeomorph _ (isSheafy_dualQuotient p)).symm
    ((dualReducedToPadicHom p).spaComap ⟨(nonempty_spa_padicPair p).some,
      (nonempty_spa_padicPair p).some_mem⟩)

/-- The squaring morphism `Spa(ℚ_[p]⟨S⟩, ℤ_[p]⟨S⟩) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` (`T ↦ S²`) is
neither étale nor finite étale (for every prime `p`, including `p = 2`). -/
example :
    let sqPair : Pair.Hom (padicDiscPair p) (padicDiscPair p) :=
      Pair.polydisc.evalHom ((padicPair p).weightedCompletionHom isWeightFamily_one_weight)
        fun _ ↦ ⟨Pair.polydiscVar 1 ℚ_[p] 0 ^ 2,
          Subring.pow_mem _ ((padicPair p).polydiscVar_mem_polydiscPlus 1 0) 2⟩
    let sq := AdicSpace.comapOfPair (isSheafy_padicDiscPair p) (isSheafy_padicDiscPair p) sqPair
    ¬ IsEtaleLocalDescription sq ∧ ¬ IsFiniteEtale sq := by
  intro sqPair sq
  suffices hnot : ¬ IsEtaleLocalDescription sq from ⟨hnot, fun h ↦ hnot (.of_isFiniteEtale h)⟩
  intro hsq
  have _ : T0Space (dualNumbers p) := t0Space_dualNumbers p
  have _ : T0Space (dualNumbers p ⧸ dualNilIdeal p) := t0Space_dualQuotient p
  let _ : UniformSpace (dualNumbers p) := IsTopologicalAddGroup.rightUniformSpace (dualNumbers p)
  have _ : IsUniformAddGroup (dualNumbers p) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (dualNumbers p) :=
    QuotientAddGroup.completeSpace_right _ (sqZeroIdeal p).toAddSubgroup
  have _ : Subsingleton (AdicSpace.ofPair (dualPair p) (isSheafy_dualPair p)).obj :=
    subsingleton_ofPair_dualPair p
  let baseHom := (Pair.quotientHom (padicDiscPair p) (sqZeroIdeal p)).comp
    ((padicPair p).weightedCompletionHom isWeightFamily_one_weight)
  let σ₁ := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ (0 : (dualPair p).plus))
  let σ₂ := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ ⟨dualEps p, dualEps_mem_plus p⟩)
  let g₁ := AdicSpace.comapOfPair (isSheafy_padicDiscPair p) (isSheafy_dualPair p) σ₁
  let g₂ := AdicSpace.comapOfPair (isSheafy_padicDiscPair p) (isSheafy_dualPair p) σ₂
  have hf_eq : g₁ ≫ sq = g₂ ≫ sq := by
    rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]
    congr 1
    refine Pair.polydisc.hom_ext ?_ fun i ↦ ?_
    · simp [Pair.Hom.comp_assoc, sqPair, σ₁, σ₂]
    · fin_cases i
      simp [sqPair, σ₁, σ₂, dualEps_sq]
  have hι_eq : AdicSpace.comapOfPair (isSheafy_dualPair p) (isSheafy_dualQuotient p)
        (Pair.quotientHom (dualPair p) (dualNilIdeal p)) ≫ g₁ =
      AdicSpace.comapOfPair (isSheafy_dualPair p) (isSheafy_dualQuotient p)
        (Pair.quotientHom (dualPair p) (dualNilIdeal p)) ≫ g₂ := by
    rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]
    congr 1
    refine Pair.polydisc.hom_ext ?_ fun i ↦ ?_
    · simp [Pair.Hom.comp_assoc, σ₁, σ₂]
    · fin_cases i
      simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply,
        Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero,
        Pair.Hom.toRingHom_quotientHom, σ₁, σ₂]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)).symm
  have hg_eq : g₁ = g₂ :=
    hsq.eq_of_sqZero_quotient (dualPair p) (isSheafy_dualPair p) (dualNilIdeal p)
      (dualNilIdeal_sq p) (isClosed_dualNilIdeal p)
      (isSheafy_dualQuotient p) (dualReducedPoint p) hf_eq hι_eq
  have hσ_eq : σ₁ = σ₂ := by
    simpa only [g₁, g₂, AdicSpace.ofPairHomEquiv_comapOfPair] using
      congrArg (AdicSpace.ofPairHomEquiv (isSheafy_padicDiscPair p) (isSheafy_dualPair p)) hg_eq
  have h0 := congrArg (fun φ : Pair.Hom _ _ ↦ φ.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0)) hσ_eq
  simp only [σ₁, σ₂, Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero] at h0
  exact dualEps_ne_zero p h0.symm

/-- The origin closed immersion `Spa(ℚ_[p], ℤ_[p]) ⟶ Spa(ℚ_[p]⟨T⟩, ℤ_[p]⟨T⟩)` at `T = 0` is
neither étale nor finite étale. -/
example :
    let originPair : Pair.Hom (padicDiscPair p) (padicPair p) :=
      Pair.polydisc.evalHom (Pair.Hom.id (padicPair p)) fun _ ↦ 0
    let origin := AdicSpace.comapOfPair (isSheafy_padicDiscPair p) (isSheafy_padicPair p) originPair
    ¬ IsEtaleLocalDescription origin ∧ ¬ IsFiniteEtale origin := by
  intro originPair origin
  suffices hnot : ¬ IsEtaleLocalDescription origin from ⟨hnot, fun h ↦ hnot (.of_isFiniteEtale h)⟩
  intro horig
  have _ : T0Space (dualNumbers p) := t0Space_dualNumbers p
  have _ : T0Space (dualNumbers p ⧸ dualNilIdeal p) := t0Space_dualQuotient p
  let _ : UniformSpace (dualNumbers p) := IsTopologicalAddGroup.rightUniformSpace (dualNumbers p)
  have _ : IsUniformAddGroup (dualNumbers p) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (dualNumbers p) :=
    QuotientAddGroup.completeSpace_right _ (sqZeroIdeal p).toAddSubgroup
  have _ : Subsingleton (AdicSpace.ofPair (dualPair p) (isSheafy_dualPair p)).obj :=
    subsingleton_ofPair_dualPair p
  let baseHom := (Pair.quotientHom (padicDiscPair p) (sqZeroIdeal p)).comp
    ((padicPair p).weightedCompletionHom isWeightFamily_one_weight)
  let hPair := Pair.polydisc.evalHom baseHom (fun _ : Fin 1 ↦ ⟨dualEps p, dualEps_mem_plus p⟩)
  let g₀Pair := (Pair.quotientHom (dualPair p) (dualNilIdeal p)).comp
    ((Pair.quotientHom (padicDiscPair p) (sqZeroIdeal p)).comp
      ((padicPair p).weightedCompletionHom isWeightFamily_one_weight))
  let g₀ := AdicSpace.comapOfPair (isSheafy_padicPair p) (isSheafy_dualQuotient p) g₀Pair
  let h := AdicSpace.comapOfPair (isSheafy_padicDiscPair p) (isSheafy_dualPair p) hPair
  have hsq : g₀ ≫ origin =
      AdicSpace.comapOfPair (isSheafy_dualPair p) (isSheafy_dualQuotient p)
        (Pair.quotientHom (dualPair p) (dualNilIdeal p)) ≫ h := by
    rw [← AdicSpace.comapOfPair_comp, ← AdicSpace.comapOfPair_comp]
    congr 1
    refine Pair.polydisc.hom_ext ?_ fun i ↦ ?_
    · simp [Pair.Hom.comp_assoc, originPair, hPair, g₀Pair, baseHom]
    · fin_cases i
      simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, originPair, hPair,
        Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero,
        Pair.Hom.toRingHom_quotientHom]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)).symm
  obtain ⟨g, _, hgf⟩ :=
    horig.exists_of_sqZero_quotient (dualPair p) (isSheafy_dualPair p) (dualNilIdeal p)
      (dualNilIdeal_sq p) (isClosed_dualNilIdeal p)
      (isSheafy_dualQuotient p) (dualReducedPoint p) g₀ h hsq
  have hpair := congrArg (AdicSpace.ofPairHomEquiv (isSheafy_padicDiscPair p) (isSheafy_dualPair p))
    hgf
  rw [AdicSpace.ofPairHomEquiv_comp, AdicSpace.ofPairHomEquiv_comapOfPair,
    AdicSpace.ofPairHomEquiv_comapOfPair] at hpair
  have h0 := congrArg (fun φ : Pair.Hom _ _ ↦ φ.toRingHom (Pair.polydiscVar 1 ℚ_[p] 0)) hpair
  simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply, originPair, hPair,
    Pair.polydisc.toRingHom_evalHom_polydiscVar, ZeroMemClass.coe_zero, map_zero] at h0
  exact dualEps_ne_zero p h0.symm

end InfinitesimalObstructions

end TauCeti.AdicSpace.Examples

end
