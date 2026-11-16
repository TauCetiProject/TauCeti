/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Right
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
import Mathlib.Tactic.Abel

/-!
# Vogt's lemma and the ring-level homotopy-equivalence criterion for A-infinity morphisms

Proves Vogt's lemma (`TauCeti.AInfinityHom.homotopyOfRightHomotopy`), upgrades
`LinearHomotopyInverse f` to `HomotopyEquiv AA BB`, and proves
`f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f)`.

## References
* R. M. Vogt, *Homotopy limits and colimits*, Math. Z. 134 (1973), 11--52.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Theorem 1.3.1.2.
-/

public section
namespace TauCeti
open ReducedTensorWords
universe uR uA uB uC
namespace AInfinityHom
variable {R : Type uR} [CommRing R]

section Vogt
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

private noncomputable def adjointHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hB : B →ₗ[R] B) (hA : A →ₗ[R] A) : A →ₗ[R] A :=
  hA ∘ₗ (LinearMap.id - g.linearPart ∘ₗ f.linearPart) + g.linearPart ∘ₗ hB ∘ₗ f.linearPart
private theorem isHomogeneous_adjointHomotopy {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (adjointHomotopy f g hR.linearHomotopy hA) AA.grading.piece
      AA.grading.piece (-1) :=
  (hhA.compOfEq ((LinearMap.isHomogeneous_id _).sub
    (g.isHomogeneous_linearPart.compOfEq f.isHomogeneous_linearPart 0)) (-1)).add
    (g.isHomogeneous_linearPart.compOfEq
      (hR.isHomogeneous_linearHomotopy.compOfEq f.isHomogeneous_linearPart (-1)) (-1))
private theorem diff_apply_of_chain_eq {M : Type*} [AddCommGroup M] [Module R M]
    {d f' h : M →ₗ[R] M} (heq : f' - LinearMap.id = d ∘ₗ h + h ∘ₗ d) (x : M) :
    d (h x) = f' x - x - h (d x) := by
  have hx := LinearMap.congr_fun heq x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    at hx
  exact eq_sub_of_add_eq hx.symm
private theorem adjointHomotopy_chain_eq {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ adjointHomotopy f g hR.linearHomotopy hA +
        adjointHomotopy f g hR.linearHomotopy hA ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
        BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
      simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
    have hdf := LinearMap.congr_fun f.differential_comp_linearPart
    have hdg := LinearMap.congr_fun g.differential_comp_linearPart
    simp only [LinearMap.comp_apply] at hdf hdg
    simp only [adjointHomotopy, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, diff_apply_of_chain_eq hhA_eq, hdg, diff_apply_of_chain_eq hBeq, hdf,
      map_sub, map_add]; abel
private noncomputable def vogtTwoHomotopy (f : AInfinityHom AA BB) (hB : B →ₗ[R] B)
    (hA : A →ₗ[R] A) : A →ₗ[R] B :=
  hB ∘ₗ f.linearPart ∘ₗ hA - f.linearPart ∘ₗ hA ∘ₗ hA - hB ∘ₗ hB ∘ₗ f.linearPart
private theorem isHomogeneous_vogtTwoHomotopy {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (vogtTwoHomotopy f hR.linearHomotopy hA) AA.grading.piece
      BB.grading.piece (-2) :=
  ((hR.isHomogeneous_linearHomotopy.compOfEq (f.isHomogeneous_linearPart.compOfEq hhA (-1))
    (-2)).sub (f.isHomogeneous_linearPart.compOfEq (hhA.compOfEq hhA (-2)) (-2))).sub
    (hR.isHomogeneous_linearHomotopy.compOfEq
      (hR.isHomogeneous_linearHomotopy.compOfEq f.isHomogeneous_linearPart (-1)) (-2))
private theorem vogtTwoHomotopy_diff_eq {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    BB.differential ∘ₗ vogtTwoHomotopy f hR.linearHomotopy hA -
        vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ AA.differential =
      hR.linearHomotopy ∘ₗ f.linearPart -
        f.linearPart ∘ₗ adjointHomotopy f g hR.linearHomotopy hA :=
  LinearMap.ext fun a ↦ by
    have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
        BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
      simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
    have hdf := LinearMap.congr_fun f.differential_comp_linearPart
    simp only [LinearMap.comp_apply] at hdf
    simp only [vogtTwoHomotopy, adjointHomotopy, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, diff_apply_of_chain_eq hBeq, hdf,
      diff_apply_of_chain_eq hhA_eq, map_sub, map_add]; abel
private noncomputable abbrev vogtBarHA (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (ξ : ReducedTensorWords R A →ₗ[R] A) :=
  gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id ξ
private noncomputable def vogtErrQ (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (ξ : ReducedTensorWords R A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A :=
  ((g.comp f).barMap - LinearMap.id) -
    (AA.barDifferential ∘ₗ vogtBarHA f g ξ + vogtBarHA f g ξ ∘ₗ AA.barDifferential)
private noncomputable abbrev vogtBarM (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (μ : ReducedTensorWords R A →ₗ[R] B) :=
  gradedCoderivAlong (AA.grading.shift 1) 0 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap μ
private noncomputable def vogtErrS (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB))
    (ξ : ReducedTensorWords R A →ₗ[R] A) (μ : ReducedTensorWords R A →ₗ[R] B) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  (hR.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ vogtBarHA f g ξ) -
    (BB.barDifferential ∘ₗ vogtBarM f g μ - vogtBarM f g μ ∘ₗ AA.barDifferential)
private theorem isHomogeneous_vogtBarHA (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    {ξ : ReducedTensorWords R A →ₗ[R] A}
    (hξ : LinearMap.IsHomogeneous ξ (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece (-1)) :
    LinearMap.IsHomogeneous (vogtBarHA f g ξ) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) (-1) :=
  isHomogeneous_gradedCoderivAlong
    (taylor_def (g.comp f) ▸ (g.comp f).isHomogeneous_taylor) (LinearMap.isHomogeneous_id _) hξ
private theorem isHomogeneous_vogtBarM (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    {μ : ReducedTensorWords R A →ₗ[R] B}
    (hμ : LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2)) :
    LinearMap.IsHomogeneous (vogtBarM f g μ) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2) :=
  isHomogeneous_gradedCoderivAlong
    ((isHomogeneous_letter (BB.grading.shift 1)).compOfEq
      (f.isHomogeneous_barMap.compOfEq (g.comp f).isHomogeneous_barMap 0) 0)
    f.isHomogeneous_barMap hμ
private theorem isCoderiv_vogtErrQ {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    {ξ : ReducedTensorWords R A →ₗ[R] A}
    (hξ : LinearMap.IsHomogeneous ξ (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece (-1)) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 0 (g.comp f).barMap LinearMap.id
      (vogtErrQ f g ξ) :=
  ((g.comp f).isCoalgHom_barMap.isGradedCoderivationAlong_sub (isCoalgHom_id A)).sub <|
    (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      (g.comp f).isCoalgHom_barMap (isCoalgHom_id A) ξ).comp_add_comp
      (isHomogeneous_vogtBarHA f g hξ) (by decide) AA.isGradedCoderivation_barDifferential
      AA.isHomogeneous_barDifferential (by decide) AA.isGradedCoderivation_barDifferential
      (g.comp f).isHomogeneous_barMap (g.comp f).barDifferential_comp_barMap rfl
private theorem isCoderiv_vogtErrS {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB))
    {ξ : ReducedTensorWords R A →ₗ[R] A} {μ : ReducedTensorWords R A →ₗ[R] B}
    (hμ : LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2)) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 1 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap
      (vogtErrS f g hR ξ μ) := by
  have h₁ : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (hR.barHomotopy ∘ₗ f.barMap) := by
    simpa only [barMap_comp, barMap_id, LinearMap.id_comp, LinearMap.comp_assoc] using
      hR.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom f.isCoalgHom_barMap
        f.isHomogeneous_barMap
  have h₂ : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (f.barMap ∘ₗ vogtBarHA f g ξ) := by
    simpa only [LinearMap.comp_id] using f.isCoalgHom_barMap.comp_isGradedCoderivationAlong
      (isGradedCoderivationAlong_gradedCoderivAlong _ 1 (g.comp f).isCoalgHom_barMap
        (isCoalgHom_id A) ξ)
  have h₃ := (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 0
    (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap μ
    ).comp_sub_negOnePow_smul_comp (isHomogeneous_vogtBarM f g hμ)
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (by decide)
      BB.isGradedCoderivation_barDifferential
      (f.isHomogeneous_barMap.compOfEq (g.comp f).isHomogeneous_barMap 0)
      (by rw [← LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc,
        (g.comp f).barDifferential_comp_barMap, LinearMap.comp_assoc])
      f.barDifferential_comp_barMap
  rw [zero_add, show (1 * (-2) : ℤ).negOnePow = 1 by decide, Units.val_one, Int.cast_one,
    one_smul] at h₃
  exact (h₁.sub h₂).sub h₃

private structure VogtStep (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) (k : ℕ) where
  ξ : ReducedTensorWords R A →ₗ[R] A
  μ : ReducedTensorWords R A →ₗ[R] B
  isHomogeneous_ξ :
    LinearMap.IsHomogeneous ξ (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)
  isHomogeneous_μ :
    LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2)
  vanishes_Q : ∀ w ∈ filtration R A k, vogtErrQ f g ξ w = 0
  vanishes_S : ∀ w ∈ filtration R A k, vogtErrS f g hR ξ μ w = 0

namespace VogtStep
variable {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
  {hR : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}

private noncomputable abbrev errQ (V : VogtStep f g hR k) := vogtErrQ f g V.ξ
private noncomputable abbrev errS (V : VogtStep f g hR k) := vogtErrS f g hR V.ξ V.μ
private noncomputable def topQ (V : VogtStep f g hR k) : ReducedTensorWords R A →ₗ[R] A :=
  letter R A ∘ₗ V.errQ
private noncomputable def topS (V : VogtStep f g hR k) : ReducedTensorWords R A →ₗ[R] B :=
  letter R B ∘ₗ V.errS
private theorem topQ_eq_zero (V : VogtStep f g hR k) {w : ReducedTensorWords R A}
    (hw : w ∈ filtration R A k) : V.topQ w = 0 := by
  rw [topQ, LinearMap.comp_apply, V.vanishes_Q w hw, map_zero]
private theorem topS_eq_zero (V : VogtStep f g hR k) {w : ReducedTensorWords R A}
    (hw : w ∈ filtration R A k) : V.topS w = 0 := by
  rw [topS, LinearMap.comp_apply, V.vanishes_S w hw, map_zero]
private theorem errQ_apply_ofLetter (V : VogtStep f g hR k) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) : V.errQ z = ofLetter R A (V.topQ z) :=
  (isCoderiv_vogtErrQ V.isHomogeneous_ξ).apply_eq_ofLetter_of_mem_filtration
    (fun _ ↦ V.topQ_eq_zero) hz
private theorem errS_apply_ofLetter (V : VogtStep f g hR k) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) : V.errS z = ofLetter R B (V.topS z) :=
  (isCoderiv_vogtErrS hR V.isHomogeneous_μ).apply_eq_ofLetter_of_mem_filtration
    (fun _ ↦ V.topS_eq_zero) hz
private theorem topQ_closed (V : VogtStep f g hR k) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    AA.differential (V.topQ z) = V.topQ (AA.unaryBarDifferential z) := by
  have hbQ : AA.barDifferential (V.errQ z) = V.errQ (AA.barDifferential z) := by
    have h₁ := LinearMap.congr_fun AA.barDifferential_sq (vogtBarHA f g V.ξ z)
    have h₂ := LinearMap.congr_fun AA.barDifferential_sq z
    simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂, map_zero, (g.comp f).barDifferential_barMap]; abel
  have h := congrArg (letter R A) hbQ
  rw [V.errQ_apply_ofLetter hz, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, letter_ofLetter, AA.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add,
    V.vanishes_Q _ (AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
  exact h
private theorem topS_diff_eq (V : VogtStep f g hR k) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    BB.differential (V.topS z) + V.topS (AA.unaryBarDifferential z) = f.linearPart (V.topQ z) := by
  have hbS : BB.barDifferential (V.errS z) + V.errS (AA.barDifferential z) =
      f.barMap (V.errQ z) := by
    have hRz := hR.barMap_sub_barMap_apply (f.barMap z)
    have h₁ := LinearMap.congr_fun BB.barDifferential_sq (vogtBarM f g V.μ z)
    have h₂ := LinearMap.congr_fun AA.barDifferential_sq z
    simp only [vogtErrS, vogtErrQ, barMap_comp, barMap_id, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply,
      map_sub, map_add, ← f.barDifferential_barMap] at hRz h₁ h₂ ⊢
    rw [h₁, h₂, map_zero]
    exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 hRz.symm))
  have h := congrArg (letter R B) hbS
  rw [map_add, V.errS_apply_ofLetter hz, V.errQ_apply_ofLetter hz, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    letter_ofLetter, letter_ofLetter, AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
    map_add, V.vanishes_S _ (AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
  exact h
private noncomputable def deltaXi (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] A := g.linearPart ∘ₗ V.topS - hA' ∘ₗ V.topQ
private noncomputable def deltaMu (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] B :=
  -(hR.linearHomotopy ∘ₗ (V.topS - f.linearPart ∘ₗ V.deltaXi hA') +
    f.linearPart ∘ₗ hA' ∘ₗ V.deltaXi hA')
private theorem isHomogeneous_topS (V : VogtStep f g hR k) :
    LinearMap.IsHomogeneous V.topS (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have hM := isHomogeneous_vogtBarM f g V.isHomogeneous_μ
  exact (isHomogeneous_letter (BB.grading.shift 1)).compOfEq
    (((hR.isHomogeneous_barHomotopy.compOfEq f.isHomogeneous_barMap (-1)).sub
      (f.isHomogeneous_barMap.compOfEq (isHomogeneous_vogtBarHA f g V.isHomogeneous_ξ) (-1))).sub
      ((BB.isHomogeneous_barDifferential.compOfEq hM (-1)).sub
        (hM.compOfEq AA.isHomogeneous_barDifferential (-1)))) (-1)
private theorem isHomogeneous_deltaXi (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaXi hA') (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece (-1) := by
  have hHA := isHomogeneous_vogtBarHA f g V.isHomogeneous_ξ
  have hQ := (isHomogeneous_letter (AA.grading.shift 1)).compOfEq
    (((g.comp f).isHomogeneous_barMap.sub (LinearMap.isHomogeneous_id _)).sub
      ((AA.isHomogeneous_barDifferential.compOfEq hHA 0).add
        (hHA.compOfEq AA.isHomogeneous_barDifferential 0))) 0
  have hg₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 g.isHomogeneous_linearPart
  have hh₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA'
  exact (hg₁.compOfEq V.isHomogeneous_topS (-1)).sub (hh₁.compOfEq hQ (-1))
private theorem isHomogeneous_deltaMu (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaMu hA') (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA'
  have hhB₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hR.isHomogeneous_linearHomotopy
  have hdξ := V.isHomogeneous_deltaXi hhA'
  exact ((hhB₁.compOfEq (V.isHomogeneous_topS.sub (hf₁.compOfEq hdξ (-1))) (-2)).add
    (hf₁.compOfEq (hhA₁.compOfEq hdξ (-2)) (-2))).neg
private theorem differential_deltaXi_add (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    AA.differential (V.deltaXi hA' z) + V.deltaXi hA' (AA.unaryBarDifferential z) = V.topQ z := by
  have hqz := V.topQ_closed hz; have hsz := congrArg g.linearPart (V.topS_diff_eq hz)
  have hg₁ := LinearMap.congr_fun g.differential_comp_linearPart (V.topS z)
  have hAz := LinearMap.congr_fun hhA'_eq (V.topQ z)
  simp only [deltaXi, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub, map_add] at hg₁ hAz hsz ⊢
  rw [← hg₁] at hsz; rw [hqz] at hAz
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hsz hAz)))
private theorem differential_deltaMu_sub (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    BB.differential (V.deltaMu hA' z) - V.deltaMu hA' (AA.unaryBarDifferential z) =
      V.topS z - f.linearPart (V.deltaXi hA' z) := by
  set dξ := V.deltaXi hA'; set s' := V.topS - f.linearPart ∘ₗ dξ
  have hμ_def : V.deltaMu hA' = -(hR.linearHomotopy ∘ₗ s' + f.linearPart ∘ₗ hA' ∘ₗ dξ) := rfl
  have hdξ := V.differential_deltaXi_add hhA'_eq hz
  have hs'_anti : s' (AA.unaryBarDifferential z) = -BB.differential (s' z) := by
    have hsz := V.topS_diff_eq hz; have hxz := congrArg f.linearPart hdξ
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (dξ z)
    simp only [s', dξ, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, map_add] at hxz hf₁ ⊢
    rw [← hf₁] at hxz
    exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hsz hxz.symm)))
  have hgz : f.linearPart (g.linearPart (s' z)) =
      f.linearPart (hA' (dξ (AA.unaryBarDifferential z))) -
        BB.differential (f.linearPart (hA' (dξ z))) := by
    have hg : g.linearPart (s' z) =
        hA' (V.topQ z) - (g.linearPart (f.linearPart (dξ z)) - dξ z) := by
      simp only [s', dξ, deltaXi, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]; abel
    have hAz := LinearMap.congr_fun hhA'_eq (dξ z)
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (hA' (dξ z))
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hAz hf₁
    rw [hg, hAz, ← hdξ, map_sub, map_add, map_add, map_add, ← hf₁]; abel
  have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
      BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
    simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
  have hBz := LinearMap.congr_fun hBeq (s' z)
  rw [hμ_def]; change _ - _ = s' z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_neg, map_add, hs'_anti] at hBz ⊢
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hBz hgz.symm)))
private theorem deltaXi_eq_zero_of_mem_filtration (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ∀ w ∈ filtration R A k, V.deltaXi hA' w = 0 := fun _ hw ↦ by
  simp only [deltaXi, LinearMap.sub_apply, LinearMap.comp_apply, V.topQ_eq_zero hw,
    V.topS_eq_zero hw, map_zero, sub_self]
private theorem deltaMu_eq_zero_of_mem_filtration (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ∀ w ∈ filtration R A k, V.deltaMu hA' w = 0 := fun w hw ↦ by
  simp only [deltaMu, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, V.topS_eq_zero hw, V.deltaXi_eq_zero_of_mem_filtration hA' w hw,
    map_zero, sub_zero, add_zero, neg_zero]
private theorem vogtBarHA_deltaXi (V : VogtStep f g hR k) (hA' : A →ₗ[R] A)
    {u : ReducedTensorWords R A} (hu : u ∈ filtration R A (k + 1)) :
    vogtBarHA f g (V.deltaXi hA') u = ofLetter R A (V.deltaXi hA' u) :=
  gradedCoderivAlong_eq_ofLetter_of_mem_filtration _ 1 (g.comp f).isCoalgHom_barMap
    (isCoalgHom_id A) (V.deltaXi_eq_zero_of_mem_filtration hA') hu
private theorem next_vanishes_Q (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) : vogtErrQ f g (V.ξ + V.deltaXi hA') z = 0 := by
  have heq : vogtErrQ f g (V.ξ + V.deltaXi hA') z = V.errQ z -
      (AA.barDifferential (vogtBarHA f g (V.deltaXi hA') z) +
        vogtBarHA f g (V.deltaXi hA') (AA.barDifferential z)) := by
    rw [vogtErrQ, vogtBarHA,
      gradedCoderivAlong_add _ 1 (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)]
    simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      map_add]; abel
  have hhi := AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  rw [heq, V.errQ_apply_ofLetter hz, V.vogtBarHA_deltaXi hA' hz,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    V.vogtBarHA_deltaXi hA' (filtration_monotone R A k.le_succ hhi),
    V.deltaXi_eq_zero_of_mem_filtration hA' _ hhi, map_zero, add_zero,
    V.vogtBarHA_deltaXi hA' (AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    ← map_add, ← map_sub, V.differential_deltaXi_add hhA'_eq hz, sub_self, map_zero]
private theorem next_vanishes_S (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    vogtErrS f g hR (V.ξ + V.deltaXi hA') (V.μ + V.deltaMu hA') z = 0 := by
  have hM {u} (hu : u ∈ filtration R A (k + 1)) :
      vogtBarM f g (V.deltaMu hA') u = ofLetter R B (V.deltaMu hA' u) :=
    gradedCoderivAlong_eq_ofLetter_of_mem_filtration _ 0
      (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap
      (V.deltaMu_eq_zero_of_mem_filtration hA') hu
  have heq : vogtErrS f g hR (V.ξ + V.deltaXi hA') (V.μ + V.deltaMu hA') z =
      V.errS z - f.barMap (vogtBarHA f g (V.deltaXi hA') z) -
        (BB.barDifferential (vogtBarM f g (V.deltaMu hA') z) -
          vogtBarM f g (V.deltaMu hA') (AA.barDifferential z)) := by
    rw [vogtErrS, vogtBarHA,
      gradedCoderivAlong_add _ 1 (g.comp f).isCoalgHom_barMap (isCoalgHom_id A), vogtBarM,
      gradedCoderivAlong_add _ 0 (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap)
        f.isCoalgHom_barMap]
    simp only [vogtErrS, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      map_add]; abel
  have hhi := AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  rw [heq, V.errS_apply_ofLetter hz, V.vogtBarHA_deltaXi hA' hz, f.barMap_ofLetter, hM hz,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    hM (filtration_monotone R A k.le_succ hhi), V.deltaMu_eq_zero_of_mem_filtration hA' _ hhi,
    map_zero, add_zero, hM (AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    ← map_sub, ← map_sub, ← map_sub, V.differential_deltaMu_sub hhA'_eq hz, sub_self, map_zero]
end VogtStep

private noncomputable def vogtBase {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) : VogtStep f g hR 1 where
  ξ := adjointHomotopy f g hR.linearHomotopy hA ∘ₗ letter R A
  μ := vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ letter R A
  isHomogeneous_ξ := (LinearMap.isHomogeneous_shift_piece_iff.2
    (isHomogeneous_adjointHomotopy hR hhA)).compOfEq
    (isHomogeneous_letter (AA.grading.shift 1)) (-1)
  isHomogeneous_μ := (LinearMap.isHomogeneous_shift_piece_iff.2
    (isHomogeneous_vogtTwoHomotopy hR hhA)).compOfEq
    (isHomogeneous_letter (AA.grading.shift 1)) (-2)
  vanishes_Q w hw := apply_eq_zero_of_mem_filtration_one R A (LinearMap.ext fun a ↦ by
    have ha := congrArg (ofLetter R A) (LinearMap.congr_fun (adjointHomotopy_chain_eq hR hhA_eq) a)
    simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, barMap_comp, f.barMap_ofLetter, g.barMap_ofLetter,
      gradedCoderivAlong_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, map_sub, map_add] at ha ⊢
    exact sub_eq_zero.2 ha) w hw
  vanishes_S w hw := apply_eq_zero_of_mem_filtration_one R A (LinearMap.ext fun a ↦ by
    have ha := congrArg (ofLetter R B) (LinearMap.congr_fun (vogtTwoHomotopy_diff_eq hR hhA_eq) a)
    simp only [vogtErrS, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      f.barMap_ofLetter, hR.barHomotopy_ofLetter, gradedCoderivAlong_ofLetter, letter_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      map_sub] at ha ⊢
    exact sub_eq_zero.2 ha.symm) w hw
private noncomputable def vogtSeq {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) : (k : ℕ) → VogtStep f g hR k
  | 0 => let b := vogtBase hR hhA hhA_eq
      ⟨b.ξ, b.μ, b.isHomogeneous_ξ, b.isHomogeneous_μ,
        fun w hw ↦ b.vanishes_Q w (filtration_monotone R A (Nat.zero_le 1) hw),
        fun w hw ↦ b.vanishes_S w (filtration_monotone R A (Nat.zero_le 1) hw)⟩
  | 1 => vogtBase hR hhA hhA_eq
  | k + 2 =>
      let v := vogtSeq hR hhA hhA_eq (k + 1)
      let hA' := adjointHomotopy f g hR.linearHomotopy hA
      let hhA' := isHomogeneous_adjointHomotopy hR hhA
      let hhA'_eq := adjointHomotopy_chain_eq hR hhA_eq
      ⟨v.ξ + v.deltaXi hA', v.μ + v.deltaMu hA',
        v.isHomogeneous_ξ.add (v.isHomogeneous_deltaXi hhA'),
        v.isHomogeneous_μ.add (v.isHomogeneous_deltaMu hhA'),
        fun _ ↦ v.next_vanishes_Q hhA'_eq, fun _ ↦ v.next_vanishes_S hhA'_eq⟩
private theorem vogtSeq_ξ_stab {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) (k : ℕ) :
    ∀ w ∈ filtration R A k, (vogtSeq hR hhA hhA_eq (k + 1)).ξ w = (vogtSeq hR hhA hhA_eq k).ξ w
  | w, hw => by cases k with
    | zero => rfl
    | succ k => simp only [vogtSeq, LinearMap.add_apply,
        (vogtSeq hR hhA hhA_eq (k + 1)).deltaXi_eq_zero_of_mem_filtration _ w hw, add_zero]

/-- **Vogt's lemma for `A∞` algebras.** If `g : BB ⟶ AA` is a right `A∞` homotopy inverse of
`f : AA ⟶ BB` and `g₁ ∘ f₁` is chain-homotopic to `id_A` via a homogeneous degree-`-1` map `hA`,
then `g` is also a left `A∞` homotopy inverse of `f`. -/
noncomputable def homotopyOfRightHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    Homotopy (g.comp f) (AInfinityHom.id AA) :=
  let seq := vogtSeq hR hhA hhA_eq
  let vogtTaylor := stabilisingLinearMap fun k ↦ (seq k).ξ
  { barHomotopy := gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap
      (AInfinityHom.id AA).barMap vogtTaylor
    isGradedCoderivationAlong_barHomotopy :=
      isGradedCoderivationAlong_gradedCoderivAlong _ 1 (g.comp f).isCoalgHom_barMap
        (AInfinityHom.id AA).isCoalgHom_barMap vogtTaylor
    isHomogeneous_barHomotopy := isHomogeneous_gradedCoderivAlong
      (taylor_def (g.comp f) ▸ (g.comp f).isHomogeneous_taylor)
      (AInfinityHom.id AA).isHomogeneous_barMap <|
      isHomogeneous_stabilisingLinearMap (vogtSeq_ξ_stab hR hhA hhA_eq)
        fun n ↦ (seq n).isHomogeneous_ξ
    barMap_sub_barMap := LinearMap.ext fun z ↦ by
      obtain ⟨n, hn⟩ := exists_mem_filtration R A z
      have hH_eq {w} (hw : w ∈ filtration R A n) :
          gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap
            (AInfinityHom.id AA).barMap vogtTaylor w = vogtBarHA f g (seq n).ξ w :=
        gradedCoderivAlong_stabilisingLinearMap_apply
          (g.comp f).isCoalgHom_barMap (AInfinityHom.id AA).isCoalgHom_barMap
          (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)
          (vogtSeq_ξ_stab hR hhA hhA_eq) (fun _ _ ↦ rfl) (fun _ _ ↦ by rw [barMap_id]) hw
      have heq := (seq n).vanishes_Q z hn
      simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at heq ⊢
      rw [hH_eq hn, hH_eq (AA.barDifferential_mem_filtration hn), barMap_id]
      exact sub_eq_zero.1 heq }

namespace LinearHomotopyInverse
/-- The left `A∞` homotopy from `L.homotopyInverse.comp f` to `AInfinityHom.id AA`. -/
noncomputable def homotopyHomotopyInverseComp {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) : Homotopy (L.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  homotopyOfRightHomotopy f L.homotopyInverse L.homotopyCompHomotopyInverse
    L.isHomogeneous_homotopyLeft (L.linearPart_homotopyInverse.symm ▸ L.inv_comp_linearPart_sub_id)

/-- Bundled two-sided `A∞` homotopy equivalence associated to `LinearHomotopyInverse f`. -/
noncomputable def homotopyEquiv {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    HomotopyEquiv AA BB :=
  ⟨f, L.homotopyInverse, L.homotopyHomotopyInverseComp, L.homotopyCompHomotopyInverse⟩

@[simp] theorem homotopyEquiv_hom {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.hom = f := (rfl)
@[simp] theorem homotopyEquiv_inv {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.inv = L.homotopyInverse := (rfl)
@[simp] theorem barHomotopy_homotopyEquiv_homotopyInvCompHom {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.homotopyInvCompHom.barHomotopy =
      L.homotopyHomotopyInverseComp.barHomotopy := (rfl)
@[simp] theorem barHomotopy_homotopyEquiv_homotopyHomCompInv {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.homotopyHomCompInv.barHomotopy =
      L.homotopyCompHomotopyInverse.barHomotopy := (rfl)
end LinearHomotopyInverse
end Vogt

namespace HomotopyEquiv
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- Transitivity of `A∞` homotopy equivalences, with forward morphism `e₂.hom.comp e₁.hom`. -/
noncomputable def trans (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    HomotopyEquiv AA CC :=
  (e₂.linearHomotopyInverse.comp e₁.linearHomotopyInverse).homotopyEquiv

@[simp] theorem trans_hom (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).hom = e₂.hom.comp e₁.hom := (rfl)
@[simp] theorem linearPart_trans_inv (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).inv.linearPart = e₁.inv.linearPart ∘ₗ e₂.inv.linearPart := by
  simp only [trans, LinearHomotopyInverse.homotopyEquiv_inv,
    LinearHomotopyInverse.linearPart_homotopyInverse, LinearHomotopyInverse.comp_inv,
    linearHomotopyInverse_inv]
end HomotopyEquiv

section IsHomotopyEquiv
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- An `A∞` morphism is a **homotopy equivalence** when it admits an `A∞` morphism in the
reverse direction whose left and right composites with it are homotopic to the identities. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA, Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
    Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ g : AInfinityHom BB AA,
      Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
        Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) := Iff.rfl
theorem HomotopyEquiv.isHomotopyEquiv_hom (e : HomotopyEquiv AA BB) : e.hom.IsHomotopyEquiv :=
  ⟨e.inv, ⟨e.homotopyInvCompHom⟩, ⟨e.homotopyHomCompInv⟩⟩
theorem HomotopyEquiv.isHomotopyEquiv_inv (e : HomotopyEquiv AA BB) : e.inv.IsHomotopyEquiv :=
  ⟨e.hom, ⟨e.homotopyHomCompInv⟩, ⟨e.homotopyInvCompHom⟩⟩

/-- **Over any commutative ring, an `A∞` morphism is a homotopy equivalence if and only if its
linear part admits a homogeneous chain-homotopy inverse.** -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f) :=
  ⟨fun ⟨g, ⟨hL⟩, ⟨hR⟩⟩ ↦ ⟨(HomotopyEquiv.mk f g hL hR).linearHomotopyInverse⟩,
    fun ⟨L⟩ ↦ L.homotopyEquiv.isHomotopyEquiv_hom⟩
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv :=
  let ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf; ⟨g, ⟨Homotopy.ofEq hg₁⟩, ⟨Homotopy.ofEq hg₂⟩⟩
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso :=
  let ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := (isHomotopyEquiv_def f).1 hf; (HomotopyEquiv.mk f g hL hR).isQuasiIso_hom
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  simp only [isHomotopyEquiv_iff_nonempty_linearHomotopyInverse]
  exact ⟨fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverse L⟩, fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverseSymm L⟩⟩
@[simp] theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, ⟨Homotopy.ofEq (comp_id _)⟩, ⟨Homotopy.ofEq (comp_id _)⟩⟩
theorem IsHomotopyEquiv.comp {C : Type uC} [AddCommGroup C] [Module R C]
    {CC : AInfinityAlgebra R C} {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv :=
  let ⟨Lg⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse g).1 hg
  let ⟨Lf⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse f).1 hf
  (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse _).2 ⟨Lg.comp Lf⟩
end IsHomotopyEquiv
end AInfinityHom
end TauCeti
