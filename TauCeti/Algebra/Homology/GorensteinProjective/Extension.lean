/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Horseshoe
public import TauCeti.Algebra.Homology.ShortComplex.Splice
public import TauCeti.Algebra.Homology.TotallyAcyclic.Extension
import TauCeti.CategoryTheory.Exact.Projective

/-!
# Extensions of Gorenstein-projective modules

Gorenstein-projective modules are closed under extensions. Given complete resolutions of the
outer terms of a short exact sequence, the projective and copresentation horseshoe steps assemble
them into a degreewise split short exact sequence of complete resolutions. The middle resolution
is totally acyclic, so its degree-zero cycles identify with the middle module.

Thus finitely generated Gorenstein-projective modules inherit the canonical exact structure from
modules. This is the first ingredient in making their exact category Frobenius.
The ring and module universes are independent under the standard smallness hypothesis needed to
iterate the positive horseshoe step.

## Main results

* `TauCeti.isGorensteinProjective_X₂_of_shortExact`: the middle term of a short exact sequence
  of Gorenstein-projective modules is Gorenstein-projective.
* `TauCeti.IsGorensteinProjective.isExtensionClosed`: Gorenstein-projective modules are extension
  closed for the canonical abelian exact structure.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti

variable {A : Type u} [Ring A] [Small.{v} A]

private structure CycleExtension
    (P Q : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ) where
  S : ShortComplex (ModuleCat.{v} A)
  shortExact : S.ShortExact
  leftIso : S.X₁ ≅ P.cycles n
  rightIso : S.X₃ ≅ Q.cycles n

private noncomputable abbrev CycleExtension.cast
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} {m n : ℤ}
    (U : CycleExtension P Q m) (h : m = n) : CycleExtension P Q n where
  S := U.S
  shortExact := U.shortExact
  leftIso := U.leftIso ≪≫ eqToIso (congrArg (fun k ↦ P.cycles k) h)
  rightIso := U.rightIso ≪≫ eqToIso (congrArg (fun k ↦ Q.cycles k) h)

private noncomputable abbrev CycleExtension.castMiddleIso
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} {m n : ℤ}
    (U : CycleExtension P Q m) (h : m = n) : (U.cast h).S.X₂ ≅ U.S.X₂ :=
  Iso.refl _

omit [Small.{v} A] in
private theorem CycleExtension.f_castMiddleIso_inv
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} {m n : ℤ}
    (U : CycleExtension P Q m) (h : m = n) :
    U.S.f ≫ (U.castMiddleIso h).inv = (U.cast h).S.f := by
  subst n
  simp

omit [Small.{v} A] in
private theorem CycleExtension.cast_f_castMiddleIso_hom
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} {m n : ℤ}
    (U : CycleExtension P Q m) (h : m = n) :
    (U.cast h).S.f ≫ (U.castMiddleIso h).hom = U.S.f := by
  subst n
  simp

omit [Small.{v} A] in
private theorem CycleExtension.cast_g_iCycles
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} {m n : ℤ}
    (U : CycleExtension P Q m) (h : m = n) :
    (U.castMiddleIso h).hom ≫ U.S.g ≫ U.rightIso.hom ≫ Q.iCycles m =
      (U.cast h).S.g ≫ (U.cast h).rightIso.hom ≫ Q.iCycles n ≫
        eqToHom (congrArg (fun k ↦ Q.X k) h.symm) := by
  subst n
  simp

private structure HorseshoeStep
    (P Q : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ)
    (U : CycleExtension P Q n) (V : CycleExtension P Q (n + 1)) where
  presentation : ShortComplex (ModuleCat.{v} A)
  shortExact : presentation.ShortExact
  sourceIso : presentation.X₁ ≅ U.S.X₂
  middleIso : presentation.X₂ ≅ P.X n ⊞ Q.X n
  targetIso : presentation.X₃ ≅ V.S.X₂
  left_f : U.S.f ≫ sourceIso.inv ≫ presentation.f ≫ middleIso.hom =
    U.leftIso.hom ≫ P.iCycles n ≫ biprod.inl
  right_f : sourceIso.inv ≫ presentation.f ≫ middleIso.hom ≫ biprod.snd =
    U.S.g ≫ U.rightIso.hom ≫ Q.iCycles n
  left_g : biprod.inl ≫ middleIso.inv ≫ presentation.g ≫ targetIso.hom =
    P.toCycles n (n + 1) ≫ V.leftIso.inv ≫ V.S.f
  right_g : middleIso.inv ≫ presentation.g ≫ targetIso.hom ≫ V.S.g ≫
      V.rightIso.hom = biprod.snd ≫ Q.toCycles n (n + 1)

private theorem positiveHorseshoeStep_nonempty
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (U : CycleExtension P Q n) :
    ∃ V : CycleExtension P Q (n + 1), Nonempty (HorseshoeStep P Q n U V) := by
  let iP := U.leftIso.hom ≫ P.iCycles n
  let iQ := U.rightIso.hom ≫ Q.iCycles n
  let pP := P.toCycles n (n + 1)
  let pQ := Q.toCycles n (n + 1)
  have hPi : iP ≫ pP = 0 := by
    dsimp [iP, pP]
    rw [Category.assoc, P.iCycles_toCycles, comp_zero]
  have hQi : iQ ≫ pQ = 0 := by
    dsimp [iQ, pQ]
    rw [Category.assoc, Q.iCycles_toCycles, comp_zero]
  let SP₀ := ShortComplex.mk (P.iCycles n) (P.toCycles n (n + 1))
    (P.iCycles_toCycles n (n + 1))
  let SP := ShortComplex.mk iP pP hPi
  let SQ₀ := ShortComplex.mk (Q.iCycles n) (Q.toCycles n (n + 1))
    (Q.iCycles_toCycles n (n + 1))
  let SQ := ShortComplex.mk iQ pQ hQi
  have hPS₀ : SP₀.ShortExact := by
    simpa only [SP₀, ← HomologicalComplex.cyclesShortComplex_def] using
      P.cyclesShortComplex_shortExact n (n + 1) (by simp) (hP.acyclic (n + 1))
  have hQS₀ : SQ₀.ShortExact := by
    simpa only [SQ₀, ← HomologicalComplex.cyclesShortComplex_def] using
      Q.cyclesShortComplex_shortExact n (n + 1) (by simp) (hQ.acyclic (n + 1))
  have hPS : (ShortComplex.mk iP pP hPi).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := SP₀) (S₂ := SP)
      (ShortComplex.isoMk U.leftIso.symm (Iso.refl _) (Iso.refl _)
        (by simp [SP₀, SP, iP]) (by simp [SP₀, SP, pP])) hPS₀
  have hQS : (ShortComplex.mk iQ pQ hQi).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := SQ₀) (S₂ := SQ)
      (ShortComplex.isoMk U.rightIso.symm (Iso.refl _) (Iso.refl _)
        (by simp [SQ₀, SQ, iQ]) (by simp [SQ₀, SQ, pQ])) hQS₀
  have hright : IsGorensteinProjective A U.S.X₃ :=
    (IsGorensteinProjective A).prop_of_iso U.rightIso.symm
      (hQ.isGorensteinProjective_cycles n)
  have := hP.finite n
  have := hQ.finite n
  have := hP.projective n
  have := hQ.projective n
  obtain ⟨K, i, p, hip, a, b, hab, hT, hV, hleftf, hrightf, hleftg, hrightg⟩ :=
    hright.exists_copresentation_horseshoe U.shortExact hPS hQS
  let V : CycleExtension P Q (n + 1) :=
    ⟨ShortComplex.mk a b hab, hV, Iso.refl _, Iso.refl _⟩
  refine ⟨V, ⟨⟨ShortComplex.mk i p hip, hT, Iso.refl _, Iso.refl _, Iso.refl _,
    ?_, ?_, ?_, ?_⟩⟩⟩
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, iP] using hleftf
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, iQ] using hrightf
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, pP, V] using hleftg
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, pQ, V] using hrightg

private noncomputable def positiveNext
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (U : CycleExtension P Q n) :
    CycleExtension P Q (n + 1) :=
  Classical.choose (positiveHorseshoeStep_nonempty hP hQ U)

private noncomputable def positiveStep
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (U : CycleExtension P Q n) :
    HorseshoeStep P Q n U (positiveNext hP hQ U) :=
  Classical.choice (Classical.choose_spec (positiveHorseshoeStep_nonempty hP hQ U))

omit [Small.{v} A] in
private theorem negativeHorseshoeStep_nonempty
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (V : CycleExtension P Q (n + 1)) :
    ∃ U : CycleExtension P Q n, Nonempty (HorseshoeStep P Q n U V) := by
  let pP := P.toCycles n (n + 1) ≫ V.leftIso.inv
  let pQ := Q.toCycles n (n + 1) ≫ V.rightIso.inv
  have hPi : P.iCycles n ≫ pP = 0 := by
    dsimp [pP]
    rw [P.iCycles_toCycles_assoc, zero_comp]
  have hQi : Q.iCycles n ≫ pQ = 0 := by
    dsimp [pQ]
    rw [Q.iCycles_toCycles_assoc, zero_comp]
  let SP₀ := ShortComplex.mk (P.iCycles n) (P.toCycles n (n + 1))
    (P.iCycles_toCycles n (n + 1))
  let SP := ShortComplex.mk (P.iCycles n) pP hPi
  let SQ₀ := ShortComplex.mk (Q.iCycles n) (Q.toCycles n (n + 1))
    (Q.iCycles_toCycles n (n + 1))
  let SQ := ShortComplex.mk (Q.iCycles n) pQ hQi
  have hPS₀ : SP₀.ShortExact := by
    simpa only [SP₀, ← HomologicalComplex.cyclesShortComplex_def] using
      P.cyclesShortComplex_shortExact n (n + 1) (by simp) (hP.acyclic (n + 1))
  have hQS₀ : SQ₀.ShortExact := by
    simpa only [SQ₀, ← HomologicalComplex.cyclesShortComplex_def] using
      Q.cyclesShortComplex_shortExact n (n + 1) (by simp) (hQ.acyclic (n + 1))
  have hPS : (ShortComplex.mk (P.iCycles n) pP hPi).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := SP₀) (S₂ := SP)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) V.leftIso.symm
        (by simp [SP₀, SP]) (by simp [SP₀, SP, pP])) hPS₀
  have hQS : (ShortComplex.mk (Q.iCycles n) pQ hQi).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := SQ₀) (S₂ := SQ)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) V.rightIso.symm
        (by simp [SQ₀, SQ]) (by simp [SQ₀, SQ, pQ])) hQS₀
  have hconf := (ExactStructure.abelian_conflation V.S).mpr V.shortExact
  obtain ⟨K, i, p, hip, a, b, hab, hT, hU, hleftg, hrightg, hleftf, hrightf⟩ :=
    (ExactStructure.abelian (ModuleCat.{v} A)).exists_conflation_biprod_of_conflation_of_projective
      hconf ((ExactStructure.abelian_conflation _).mpr hPS)
      ((ExactStructure.abelian_conflation _).mpr hQS)
      ((ExactStructure.abelian_isProjective_iff _).mpr (hQ.projective n))
  let U : CycleExtension P Q n :=
    ⟨ShortComplex.mk a b hab, (ExactStructure.abelian_conflation _).mp hU,
      Iso.refl _, Iso.refl _⟩
  refine ⟨U, ⟨⟨ShortComplex.mk i p hip, (ExactStructure.abelian_conflation _).mp hT,
    Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_, ?_, ?_⟩⟩⟩
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, U] using hleftf
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, U] using hrightf
  · simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
      Category.assoc, pP] using hleftg
  · simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    rw [← Category.assoc, hrightg]
    simp [pQ]

private noncomputable def negativePrevious
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (V : CycleExtension P Q (n + 1)) :
    CycleExtension P Q n :=
  Classical.choose (negativeHorseshoeStep_nonempty hP hQ V)

private noncomputable def negativeStep
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) {n : ℤ} (V : CycleExtension P Q (n + 1)) :
    HorseshoeStep P Q n (negativePrevious hP hQ V) V :=
  Classical.choice (Classical.choose_spec (negativeHorseshoeStep_nonempty hP hQ V))

private noncomputable abbrev positiveState
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    (n : ℕ) → CycleExtension P Q (n : ℤ)
  | 0 => U
  | n + 1 =>
      (positiveNext hP hQ (positiveState hP hQ U n)).cast (by omega)

private noncomputable def positiveStepAt
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :=
  positiveStep hP hQ (positiveState hP hQ U n)

private noncomputable def positiveNextMiddleIso
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (positiveState hP hQ U (n + 1)).S.X₂ ≅
      (positiveNext hP hQ (positiveState hP hQ U n)).S.X₂ :=
  CycleExtension.castMiddleIso
    (positiveNext hP hQ (positiveState hP hQ U n)) (by omega)

private theorem positive_f_connect
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (positiveNext hP hQ (positiveState hP hQ U n)).S.f ≫
        (positiveNextMiddleIso hP hQ U n).inv =
      (positiveState hP hQ U (n + 1)).S.f := by
  apply CycleExtension.f_castMiddleIso_inv

private theorem positive_g_iCycles_connect
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (positiveNextMiddleIso hP hQ U n).inv ≫
        (positiveState hP hQ U (n + 1)).S.g ≫
        (positiveState hP hQ U (n + 1)).rightIso.hom ≫ Q.iCycles (n + 1 : ℕ) =
      (positiveNext hP hQ (positiveState hP hQ U n)).S.g ≫
        (positiveNext hP hQ (positiveState hP hQ U n)).rightIso.hom ≫
          Q.iCycles ((n : ℤ) + 1) := by
  simp [positiveNextMiddleIso, positiveState, CycleExtension.cast]

private noncomputable abbrev negativeState
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    (n : ℕ) → CycleExtension P Q (-(n : ℤ))
  | 0 => U
  | n + 1 => negativePrevious hP hQ ((negativeState hP hQ U n).cast (by omega))

private noncomputable abbrev negativeCurrent
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    CycleExtension P Q (-((n + 1 : ℕ) : ℤ) + 1) :=
  (negativeState hP hQ U n).cast (by omega)

private noncomputable def negativeStepAt
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :=
  negativeStep hP hQ (negativeCurrent hP hQ U n)

private noncomputable def negativeCurrentMiddleIso
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (negativeCurrent hP hQ U n).S.X₂ ≅ (negativeState hP hQ U n).S.X₂ :=
  CycleExtension.castMiddleIso (negativeState hP hQ U n) (by omega)

omit [Small.{v} A] in
private theorem negative_f_connect
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (negativeCurrent hP hQ U n).S.f ≫
        (negativeCurrentMiddleIso hP hQ U n).hom =
      (negativeState hP hQ U n).S.f := by
  apply CycleExtension.cast_f_castMiddleIso_hom

omit [Small.{v} A] in
private theorem negative_g_iCycles_connect
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℕ) :
    (negativeCurrentMiddleIso hP hQ U n).hom ≫
        (negativeState hP hQ U n).S.g ≫
        (negativeState hP hQ U n).rightIso.hom ≫ Q.iCycles (-(n : ℤ)) =
      (negativeCurrent hP hQ U n).S.g ≫
        (negativeCurrent hP hQ U n).rightIso.hom ≫
          Q.iCycles (-((n + 1 : ℕ) : ℤ) + 1) ≫
            eqToHom (congrArg (fun k ↦ Q.X k) (by omega)) := by
  apply CycleExtension.cast_g_iCycles

private noncomputable def completeHorseshoe
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    ℤ → ShortComplex (ModuleCat.{v} A)
  | .ofNat n => (positiveStepAt hP hQ U n).presentation
  | .negSucc n => (negativeStepAt hP hQ U n).presentation

private noncomputable def completeHorseshoeIso
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    ∀ n, (completeHorseshoe hP hQ U n).X₃ ≅
      (completeHorseshoe hP hQ U (n + 1)).X₁
  | .ofNat n => (positiveStepAt hP hQ U n).targetIso ≪≫
      (positiveNextMiddleIso hP hQ U n).symm ≪≫
      (positiveStepAt hP hQ U (n + 1)).sourceIso.symm
  | .negSucc 0 => (negativeStepAt hP hQ U 0).targetIso ≪≫
      negativeCurrentMiddleIso hP hQ U 0 ≪≫
      (positiveStepAt hP hQ U 0).sourceIso.symm
  | .negSucc (n + 1) => (negativeStepAt hP hQ U (n + 1)).targetIso ≪≫
      negativeCurrentMiddleIso hP hQ U (n + 1) ≪≫
      (negativeStepAt hP hQ U n).sourceIso.symm

private noncomputable def completeMiddleIso
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    ∀ n, (completeHorseshoe hP hQ U n).X₂ ≅ P.X n ⊞ Q.X n
  | .ofNat n => (positiveStepAt hP hQ U n).middleIso
  | .negSucc n => (negativeStepAt hP hQ U n).middleIso

private theorem completeHorseshoe_shortExact
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℤ) :
    (completeHorseshoe hP hQ U n).ShortExact := by
  cases n with
  | ofNat n => exact (positiveStepAt hP hQ U n).shortExact
  | negSucc n => exact (negativeStepAt hP hQ U n).shortExact

private noncomputable abbrev completeHorseshoeComplex
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :=
  CochainComplex.splice (completeHorseshoe hP hQ U) (completeHorseshoeIso hP hQ U)

private theorem completeHorseshoeComplex_d
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℤ) :
    (completeHorseshoeComplex hP hQ U).d n (n + 1) =
      (completeHorseshoe hP hQ U n).g ≫ (completeHorseshoeIso hP hQ U n).hom ≫
        (completeHorseshoe hP hQ U (n + 1)).f :=
  CochainComplex.splice_d _ _ n

private theorem completeHorseshoe_left_comm
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℤ) :
    (biprod.inl ≫ (completeMiddleIso hP hQ U n).inv) ≫
        (completeHorseshoeComplex hP hQ U).d n (n + 1) =
      P.d n (n + 1) ≫ biprod.inl ≫ (completeMiddleIso hP hQ U (n + 1)).inv := by
  rw [completeHorseshoeComplex_d]
  rw [← cancel_mono (completeMiddleIso hP hQ U (n + 1)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Expose the three integer-constructor cases so adjacent recursive states have matching indices.
  -- In each case, `change` only unfolds the constructor clauses of `completeHorseshoe`,
  -- `completeHorseshoeIso` and `completeMiddleIso`, writing the goal as a composite of the
  -- horseshoe-step fields whose compatibility equations are then rewritten.
  cases n with
  | ofNat n =>
      change biprod.inl ≫ (positiveStepAt hP hQ U n).middleIso.inv ≫
          (positiveStepAt hP hQ U n).presentation.g ≫
          (positiveStepAt hP hQ U n).targetIso.hom ≫
          (positiveNextMiddleIso hP hQ U n).inv ≫
          (positiveStepAt hP hQ U (n + 1)).sourceIso.inv ≫
          (positiveStepAt hP hQ U (n + 1)).presentation.f ≫
          (positiveStepAt hP hQ U (n + 1)).middleIso.hom =
        P.d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ biprod.inl
      rw [reassoc_of% (positiveStepAt hP hQ U n).left_g,
        reassoc_of% positive_f_connect hP hQ U n,
        (positiveStepAt hP hQ U (n + 1)).left_f]
      simp
  | negSucc n =>
      cases n with
      | zero =>
          change biprod.inl ≫ (negativeStepAt hP hQ U 0).middleIso.inv ≫
              (negativeStepAt hP hQ U 0).presentation.g ≫
              (negativeStepAt hP hQ U 0).targetIso.hom ≫
              (negativeCurrentMiddleIso hP hQ U 0).hom ≫
              (positiveStepAt hP hQ U 0).sourceIso.inv ≫
              (positiveStepAt hP hQ U 0).presentation.f ≫
              (positiveStepAt hP hQ U 0).middleIso.hom =
            P.d (-1) 0 ≫ biprod.inl
          rw [reassoc_of% (negativeStepAt hP hQ U 0).left_g,
            reassoc_of% negative_f_connect hP hQ U 0,
            (positiveStepAt hP hQ U 0).left_f]
          simp
      | succ n =>
          change biprod.inl ≫ (negativeStepAt hP hQ U (n + 1)).middleIso.inv ≫
              (negativeStepAt hP hQ U (n + 1)).presentation.g ≫
              (negativeStepAt hP hQ U (n + 1)).targetIso.hom ≫
              (negativeCurrentMiddleIso hP hQ U (n + 1)).hom ≫
              (negativeStepAt hP hQ U n).sourceIso.inv ≫
              (negativeStepAt hP hQ U n).presentation.f ≫
              (negativeStepAt hP hQ U n).middleIso.hom =
            P.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ biprod.inl
          rw [reassoc_of% (negativeStepAt hP hQ U (n + 1)).left_g,
            reassoc_of% negative_f_connect hP hQ U (n + 1),
            (negativeStepAt hP hQ U n).left_f]
          simp only [Int.natCast_add, Int.cast_ofNat_Int, eqToIso_refl, Iso.trans_refl,
            Iso.inv_hom_id_assoc]
          -- The cycle indices `-(n + 1 + 1) + 1` and `-(n + 1)` left by the recursive states are
          -- the integer `Int.negSucc n` by evaluation; restate them as such to match `P.d`.
          change P.toCycles (Int.negSucc (n + 1)) (Int.negSucc n) ≫
              P.iCycles (Int.negSucc n) ≫ biprod.inl =
            P.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ biprod.inl
          rw [reassoc_of% P.toCycles_i]

private theorem completeHorseshoe_right_comm
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℤ) :
    (completeMiddleIso hP hQ U n).hom ≫ biprod.snd ≫ Q.d n (n + 1) =
      (completeHorseshoeComplex hP hQ U).d n (n + 1) ≫
        (completeMiddleIso hP hQ U (n + 1)).hom ≫ biprod.snd := by
  rw [completeHorseshoeComplex_d]
  rw [← cancel_epi (completeMiddleIso hP hQ U n).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- Expose the three integer-constructor cases so adjacent recursive states have matching indices.
  -- In each case, `change` only unfolds the constructor clauses of `completeHorseshoe`,
  -- `completeHorseshoeIso` and `completeMiddleIso`, writing the goal as a composite of the
  -- horseshoe-step fields whose compatibility equations are then rewritten.
  cases n with
  | ofNat n =>
      change biprod.snd ≫ Q.d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
        (positiveStepAt hP hQ U n).middleIso.inv ≫
          (positiveStepAt hP hQ U n).presentation.g ≫
          (positiveStepAt hP hQ U n).targetIso.hom ≫
          (positiveNextMiddleIso hP hQ U n).inv ≫
          (positiveStepAt hP hQ U (n + 1)).sourceIso.inv ≫
          (positiveStepAt hP hQ U (n + 1)).presentation.f ≫
          (positiveStepAt hP hQ U (n + 1)).middleIso.hom ≫ biprod.snd
      rw [(positiveStepAt hP hQ U (n + 1)).right_f,
        positive_g_iCycles_connect hP hQ U n,
        reassoc_of% (positiveStepAt hP hQ U n).right_g]
      rw [Q.toCycles_i]
      simp
  | negSucc n =>
      cases n with
      | zero =>
          change biprod.snd ≫ Q.d (-1) 0 =
            (negativeStepAt hP hQ U 0).middleIso.inv ≫
              (negativeStepAt hP hQ U 0).presentation.g ≫
              (negativeStepAt hP hQ U 0).targetIso.hom ≫
              (negativeCurrentMiddleIso hP hQ U 0).hom ≫
              (positiveStepAt hP hQ U 0).sourceIso.inv ≫
              (positiveStepAt hP hQ U 0).presentation.f ≫
              (positiveStepAt hP hQ U 0).middleIso.hom ≫ biprod.snd
          -- Zero-index identification: `positiveState 0` and `negativeState 0` are both the
          -- initial extension `U`, and `((0 : ℕ) : ℤ)` and `-((0 : ℕ) : ℤ)` both evaluate to `0`,
          -- so the two composites below agree by `rfl`; this links the positive and negative
          -- halves of the horseshoe.
          rw [(positiveStepAt hP hQ U 0).right_f,
            show (positiveState hP hQ U 0).S.g ≫
                (positiveState hP hQ U 0).rightIso.hom ≫ Q.iCycles ((0 : ℕ) : ℤ) =
              (negativeState hP hQ U 0).S.g ≫
                (negativeState hP hQ U 0).rightIso.hom ≫ Q.iCycles (-((0 : ℕ) : ℤ)) by rfl,
            negative_g_iCycles_connect hP hQ U 0,
            reassoc_of% (negativeStepAt hP hQ U 0).right_g]
          rw [reassoc_of% Q.toCycles_i]
          simp only [Nat.reduceAdd, Int.cast_ofNat_Int, Int.reduceNeg, Int.reduceAdd,
            eqToHom_refl, Category.comp_id]
      | succ n =>
          change biprod.snd ≫ Q.d (Int.negSucc (n + 1)) (Int.negSucc n) =
            (negativeStepAt hP hQ U (n + 1)).middleIso.inv ≫
              (negativeStepAt hP hQ U (n + 1)).presentation.g ≫
              (negativeStepAt hP hQ U (n + 1)).targetIso.hom ≫
              (negativeCurrentMiddleIso hP hQ U (n + 1)).hom ≫
              (negativeStepAt hP hQ U n).sourceIso.inv ≫
              (negativeStepAt hP hQ U n).presentation.f ≫
              (negativeStepAt hP hQ U n).middleIso.hom ≫ biprod.snd
          rw [(negativeStepAt hP hQ U n).right_f,
            negative_g_iCycles_connect hP hQ U (n + 1),
            reassoc_of% (negativeStepAt hP hQ U (n + 1)).right_g]
          rw [reassoc_of% Q.toCycles_i]
          have hd := Q.d_comp_XIsoOfEq_hom
            (by omega : (-((n + 1 + 1 : ℕ) : ℤ) + 1) = -((n + 1 : ℕ) : ℤ))
            (-((n + 1 + 1 : ℕ) : ℤ))
          simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom] at hd
          rw [hd]
          simp [Int.negSucc_eq]

private noncomputable def completeHorseshoeInclusion
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    P ⟶ completeHorseshoeComplex hP hQ U :=
  CochainComplex.ofHom
    (fun n ↦ biprod.inl ≫ (completeMiddleIso hP hQ U n).inv)
    (completeHorseshoe_left_comm hP hQ U)

private noncomputable def completeHorseshoeProjection
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    completeHorseshoeComplex hP hQ U ⟶ Q :=
  CochainComplex.ofHom
    (fun n ↦ (completeMiddleIso hP hQ U n).hom ≫ biprod.snd)
    (completeHorseshoe_right_comm hP hQ U)

private theorem completeHorseshoe_zero
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    completeHorseshoeInclusion hP hQ U ≫ completeHorseshoeProjection hP hQ U = 0 := by
  ext n
  simp [completeHorseshoeInclusion, completeHorseshoeProjection]

private noncomputable def completeHorseshoeShortComplex
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :=
  ShortComplex.mk (completeHorseshoeInclusion hP hQ U)
    (completeHorseshoeProjection hP hQ U) (completeHorseshoe_zero hP hQ U)

private noncomputable def completeHorseshoeSplitting
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) (n : ℤ) :
    (ShortComplex.mk ((completeHorseshoeShortComplex hP hQ U).f.f n)
      ((completeHorseshoeShortComplex hP hQ U).g.f n) (by
        rw [← HomologicalComplex.comp_f, (completeHorseshoeShortComplex hP hQ U).zero,
          HomologicalComplex.zero_f])).Splitting := by
  apply (ShortComplex.Splitting.ofHasBinaryBiproduct (P.X n) (Q.X n)).ofIso
  exact ShortComplex.isoMk (Iso.refl _) (completeMiddleIso hP hQ U n).symm (Iso.refl _)
    (by simp [completeHorseshoeShortComplex, completeHorseshoeInclusion])
    (by simp [completeHorseshoeShortComplex, completeHorseshoeProjection])

private theorem completeHorseshoe_isTotallyAcyclic
    {P Q : CochainComplex (ModuleCat.{v} A) ℤ} (hP : P.IsTotallyAcyclic)
    (hQ : Q.IsTotallyAcyclic) (U : CycleExtension P Q 0) :
    (completeHorseshoeComplex hP hQ U).IsTotallyAcyclic :=
  CochainComplex.IsTotallyAcyclic.of_degreewise_split hP hQ
    (completeHorseshoeSplitting hP hQ U)

/-- The middle term of a short exact sequence of Gorenstein-projective modules is
Gorenstein-projective. -/
theorem isGorensteinProjective_X₂_of_shortExact
    {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
    (h₁ : IsGorensteinProjective A S.X₁) (h₃ : IsGorensteinProjective A S.X₃) :
    IsGorensteinProjective A S.X₂ := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isGorensteinProjective_iff S.X₁).mp h₁
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := (isGorensteinProjective_iff S.X₃).mp h₃
  let U : CycleExtension P Q 0 := ⟨S, hS, eP.symm, eQ.symm⟩
  apply (isGorensteinProjective_iff S.X₂).mpr
  refine ⟨completeHorseshoeComplex hP hQ U,
    completeHorseshoe_isTotallyAcyclic hP hQ U, ⟨?_⟩⟩
  exact (CochainComplex.spliceCyclesIso (completeHorseshoe hP hQ U)
    (completeHorseshoeIso hP hQ U) (completeHorseshoe_shortExact hP hQ U) 0).symm ≪≫
      (positiveStepAt hP hQ U 0).sourceIso

/-- Gorenstein-projective modules are extension closed for the canonical exact structure on
modules. -/
theorem IsGorensteinProjective.isExtensionClosed :
    (ExactStructure.abelian (ModuleCat.{v} A)).IsExtensionClosed
      (IsGorensteinProjective A) :=
  (ExactStructure.isExtensionClosed_abelian_iff (IsGorensteinProjective A)).mpr
    ⟨isGorensteinProjective_X₂_of_shortExact⟩

end TauCeti
