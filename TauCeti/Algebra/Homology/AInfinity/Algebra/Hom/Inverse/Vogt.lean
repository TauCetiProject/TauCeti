/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Right
import TauCeti.LinearAlgebra.TensorCoalgebra.RelativeCoderivation
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
import Mathlib.Tactic.Abel

/-!
# Vogt's lemma and the ring-level homotopy-equivalence criterion for A-infinity morphisms

Proves Vogt's lemma for `A∞` algebras over any commutative ring: if `g : BB ⟶ AA` is a right `A∞`
homotopy inverse of `f : AA ⟶ BB` and `g₁ ∘ f₁` is chain-homotopic to `id_A`, then `g` is also a
left `A∞` homotopy inverse of `f`. Combining this with the right homotopy inverse construction
yields the ring-level characterization of `A∞` homotopy equivalences and transitivity of
`HomotopyEquiv`.

## Main definitions

* `TauCeti.AInfinityHom.homotopyOfRightHomotopy`: Vogt's lemma for `A∞` morphisms.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyHomotopyInverseComp`: left `A∞` homotopy.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyEquiv`: bundled `HomotopyEquiv`.
* `TauCeti.AInfinityHom.HomotopyEquiv.trans`: transitivity of `A∞` homotopy equivalences.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: predicate for admitting a two-sided homotopy inverse.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`: ring-level criterion.
* `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`: homotopy invariance of `IsHomotopyEquiv`.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`: closure of `IsHomotopyEquiv` under composition.

## References

* R. M. Vogt, *Homotopy limits and colimits*, Math. Z. 134 (1973), 11--52.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Theorem 1.3.1.2.
-/

namespace TauCeti
open ReducedTensorWords
universe uR uA uB uC
namespace AInfinityHom
variable {R : Type uR} [CommRing R]

section Vogt
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

section PrivateHelpers
variable {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}

private noncomputable def adjointHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hB : B →ₗ[R] B) (hA : A →ₗ[R] A) : A →ₗ[R] A :=
  hA ∘ₗ (LinearMap.id - g.linearPart ∘ₗ f.linearPart) + g.linearPart ∘ₗ hB ∘ₗ f.linearPart
private noncomputable def vogtTwoHomotopy (f : AInfinityHom AA BB) (hB : B →ₗ[R] B)
    (hA : A →ₗ[R] A) : A →ₗ[R] B :=
  hB ∘ₗ f.linearPart ∘ₗ hA - f.linearPart ∘ₗ hA ∘ₗ hA - hB ∘ₗ hB ∘ₗ f.linearPart
private noncomputable abbrev vogtBarHA (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (ξ : ReducedTensorWords R A →ₗ[R] A) :=
  gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id ξ
private noncomputable def vogtErrQ (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (ξ : ReducedTensorWords R A →ₗ[R] A) :=
  ((g.comp f).barMap - LinearMap.id) -
    (AA.barDifferential ∘ₗ vogtBarHA f g ξ + vogtBarHA f g ξ ∘ₗ AA.barDifferential)
private noncomputable abbrev vogtBarM (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (μ : ReducedTensorWords R A →ₗ[R] B) :=
  gradedCoderivAlong (AA.grading.shift 1) 0 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap μ
private noncomputable def vogtErrS (hR : Homotopy (f.comp g) (AInfinityHom.id BB))
    (ξ : ReducedTensorWords R A →ₗ[R] A) (μ : ReducedTensorWords R A →ₗ[R] B) :=
  (hR.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ vogtBarHA f g ξ) -
    (BB.barDifferential ∘ₗ vogtBarM f g μ - vogtBarM f g μ ∘ₗ AA.barDifferential)

section LinearAdjoint
variable (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}

private theorem linearPart_right_eq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
    BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
  simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
private theorem isHomogeneous_adjointHomotopy
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (adjointHomotopy f g hR.linearHomotopy hA) AA.grading.piece
      AA.grading.piece (-1) :=
  (zero_add (-1 : ℤ) ▸ hhA.comp ((LinearMap.isHomogeneous_id _).sub
    (add_zero (0 : ℤ) ▸ g.isHomogeneous_linearPart.comp f.isHomogeneous_linearPart))).add
    (add_zero (-1 : ℤ) ▸ g.isHomogeneous_linearPart.comp
      (zero_add (-1 : ℤ) ▸ hR.isHomogeneous_linearHomotopy.comp f.isHomogeneous_linearPart))
private theorem adjointHomotopy_chain_eq
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ adjointHomotopy f g hR.linearHomotopy hA +
        adjointHomotopy f g hR.linearHomotopy hA ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    have hdf := LinearMap.congr_fun f.differential_comp_linearPart
    have hdg := LinearMap.congr_fun g.differential_comp_linearPart
    have hA1 := LinearMap.congr_fun hhA_eq (a - g.linearPart (f.linearPart a))
    have hB1 := congrArg g.linearPart
      (LinearMap.congr_fun (linearPart_right_eq hR) (f.linearPart a))
    simp only [LinearMap.comp_apply] at hdf hdg
    simp only [adjointHomotopy, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add, hdg, hdf] at hA1 hB1 ⊢
    exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hA1 hB1)))
private theorem isHomogeneous_vogtTwoHomotopy
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (vogtTwoHomotopy f hR.linearHomotopy hA) AA.grading.piece
      BB.grading.piece (-2) :=
  let h₂ : (-1 : ℤ) + -1 = -2 := by decide
  ((h₂ ▸ hR.isHomogeneous_linearHomotopy.comp
      (add_zero (-1 : ℤ) ▸ f.isHomogeneous_linearPart.comp hhA)).sub
    (add_zero (-2 : ℤ) ▸ f.isHomogeneous_linearPart.comp (h₂ ▸ hhA.comp hhA))).sub
    (h₂ ▸ hR.isHomogeneous_linearHomotopy.comp
      (zero_add (-1 : ℤ) ▸ hR.isHomogeneous_linearHomotopy.comp f.isHomogeneous_linearPart))
private theorem vogtTwoHomotopy_diff_eq
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    BB.differential ∘ₗ vogtTwoHomotopy f hR.linearHomotopy hA -
        vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ AA.differential =
      hR.linearHomotopy ∘ₗ f.linearPart -
        f.linearPart ∘ₗ adjointHomotopy f g hR.linearHomotopy hA :=
  LinearMap.ext fun a ↦ by
    have hdf := LinearMap.congr_fun f.differential_comp_linearPart
    have hA' := LinearMap.congr_fun hhA_eq
    have hB' := LinearMap.congr_fun (linearPart_right_eq hR)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hdf hA' hB'
    have hdA (x) := eq_sub_of_add_eq (hA' x).symm
    have hdB (y) := eq_sub_of_add_eq (hB' y).symm
    simp only [vogtTwoHomotopy, adjointHomotopy, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, hdB, hdf, hdA, map_sub, map_add]; abel
end LinearAdjoint

private theorem isHomogeneous_vogtBarHA {ξ} (hξ : LinearMap.IsHomogeneous ξ
    (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)) :
    LinearMap.IsHomogeneous (vogtBarHA f g ξ) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) (-1) := isHomogeneous_gradedCoderivAlong
  (taylor_def (g.comp f) ▸ (g.comp f).isHomogeneous_taylor) (LinearMap.isHomogeneous_id _) hξ
private theorem isHomogeneous_vogtBarM {μ} (hμ : LinearMap.IsHomogeneous μ
    (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2)) :
    LinearMap.IsHomogeneous (vogtBarM f g μ) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2) := isHomogeneous_gradedCoderivAlong
  (add_zero (0 : ℤ) ▸ (isHomogeneous_letter (BB.grading.shift 1)).comp
    (add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap))
  f.isHomogeneous_barMap hμ
private theorem isCoderiv_vogtErrQ {ξ} (hξ : LinearMap.IsHomogeneous ξ
    (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 0 (g.comp f).barMap LinearMap.id
      (vogtErrQ f g ξ) :=
  ((g.comp f).isCoalgHom_barMap.isGradedCoderivationAlong_sub (isCoalgHom_id A)).sub <|
    (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      (g.comp f).isCoalgHom_barMap (isCoalgHom_id A) ξ).comp_add_comp (isHomogeneous_vogtBarHA hξ)
      (by decide) AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential
      (by decide) AA.isGradedCoderivation_barDifferential (g.comp f).isHomogeneous_barMap
      (g.comp f).barDifferential_comp_barMap rfl
private theorem isCoderiv_vogtErrS (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {ξ μ}
    (hμ : LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2)) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 1 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap
      (vogtErrS hR ξ μ) := by
  have h₁ := hR.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom f.isCoalgHom_barMap
    f.isHomogeneous_barMap
  rw [barMap_comp, barMap_id, LinearMap.id_comp, LinearMap.comp_assoc, ← barMap_comp] at h₁
  have h₂ := LinearMap.comp_id f.barMap ▸ f.isCoalgHom_barMap.comp_isGradedCoderivationAlong
    (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      (g.comp f).isCoalgHom_barMap (isCoalgHom_id A) ξ)
  have h₃ := (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 0
    (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap
    μ).comp_sub_negOnePow_smul_comp (isHomogeneous_vogtBarM hμ)
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (by decide)
      BB.isGradedCoderivation_barDifferential
      (add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap)
      (by rw [← LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc,
        (g.comp f).barDifferential_comp_barMap, LinearMap.comp_assoc])
      f.barDifferential_comp_barMap
  have hpow : (1 * (-2) : ℤ).negOnePow = 1 := by decide
  exact (h₁.sub h₂).sub
    (by simpa only [zero_add, hpow, Units.val_one, Int.cast_one, one_smul] using h₃)
end PrivateHelpers

private structure VogtStep {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) (k : ℕ) where
  ξ : ReducedTensorWords R A →ₗ[R] A
  μ : ReducedTensorWords R A →ₗ[R] B
  isHomogeneous_ξ :
    LinearMap.IsHomogeneous ξ (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)
  isHomogeneous_μ :
    LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2)
  vanishes_Q : ∀ w ∈ filtration R A k, vogtErrQ f g ξ w = 0
  vanishes_S : ∀ w ∈ filtration R A k, vogtErrS hR ξ μ w = 0

namespace VogtStep
variable {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
  {hR : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ} (V : VogtStep hR k)

private noncomputable abbrev errQ := vogtErrQ f g V.ξ
private noncomputable abbrev errS := vogtErrS hR V.ξ V.μ
private noncomputable def topQ : ReducedTensorWords R A →ₗ[R] A := letter R A ∘ₗ V.errQ
private noncomputable def topS : ReducedTensorWords R A →ₗ[R] B := letter R B ∘ₗ V.errS
private theorem topQ_eq_zero {w} (hw : w ∈ filtration R A k) : V.topQ w = 0 := by
  rw [topQ, LinearMap.comp_apply, V.vanishes_Q w hw, map_zero]
private theorem topS_eq_zero {w} (hw : w ∈ filtration R A k) : V.topS w = 0 := by
  rw [topS, LinearMap.comp_apply, V.vanishes_S w hw, map_zero]
private theorem errQ_apply_ofLetter {z} (hz : z ∈ filtration R A (k + 1)) :
    V.errQ z = ofLetter R A (V.topQ z) :=
  (isCoderiv_vogtErrQ V.isHomogeneous_ξ).apply_eq_ofLetter_of_mem_filtration
    (fun _ ↦ V.topQ_eq_zero) hz
private theorem errS_apply_ofLetter {z} (hz : z ∈ filtration R A (k + 1)) :
    V.errS z = ofLetter R B (V.topS z) :=
  (isCoderiv_vogtErrS hR V.isHomogeneous_μ).apply_eq_ofLetter_of_mem_filtration
    (fun _ ↦ V.topS_eq_zero) hz
private theorem topQ_closed {z} (hz : z ∈ filtration R A (k + 1)) :
    AA.differential (V.topQ z) = V.topQ (AA.unaryBarDifferential z) := by
  have herr : AA.barDifferential (V.errQ z) = V.errQ (AA.barDifferential z) := by
    have h₁ := LinearMap.congr_fun AA.barDifferential_sq (vogtBarHA f g V.ξ z)
    have h₂ := LinearMap.congr_fun AA.barDifferential_sq z
    simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂, map_zero, (g.comp f).barDifferential_barMap]; abel
  have h := congrArg (letter R A) herr
  rwa [V.errQ_apply_ofLetter hz, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, letter_ofLetter,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    V.vanishes_Q _ (AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
private theorem topS_diff_eq {z} (hz : z ∈ filtration R A (k + 1)) :
    BB.differential (V.topS z) + V.topS (AA.unaryBarDifferential z) = f.linearPart (V.topQ z) := by
  have herr : BB.barDifferential (V.errS z) + V.errS (AA.barDifferential z) =
      f.barMap (V.errQ z) := by
    have hRz := hR.barMap_sub_barMap_apply (f.barMap z)
    have h₁ := LinearMap.congr_fun BB.barDifferential_sq (vogtBarM f g V.μ z)
    have h₂ := LinearMap.congr_fun AA.barDifferential_sq z
    simp only [vogtErrS, vogtErrQ, barMap_comp, barMap_id, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply,
      map_sub, map_add, ← f.barDifferential_barMap] at hRz h₁ h₂ ⊢
    rw [h₁, h₂, map_zero]; exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 hRz.symm))
  have h := congrArg (letter R B) herr
  rwa [map_add, V.errS_apply_ofLetter hz, V.errQ_apply_ofLetter hz, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    letter_ofLetter, letter_ofLetter, AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
    map_add, V.vanishes_S _ (AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
private noncomputable def deltaXi (hA' : A →ₗ[R] A) := g.linearPart ∘ₗ V.topS - hA' ∘ₗ V.topQ
private noncomputable def deltaMu (hA' : A →ₗ[R] A) :=
  -(hR.linearHomotopy ∘ₗ (V.topS - f.linearPart ∘ₗ V.deltaXi hA') +
    f.linearPart ∘ₗ hA' ∘ₗ V.deltaXi hA')
private theorem isHomogeneous_topS : LinearMap.IsHomogeneous V.topS
    (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-1) :=
  let hM := isHomogeneous_vogtBarM V.isHomogeneous_μ
  add_zero (-1 : ℤ) ▸ (isHomogeneous_letter (BB.grading.shift 1)).comp
    (((zero_add (-1 : ℤ) ▸ hR.isHomogeneous_barHomotopy.comp f.isHomogeneous_barMap).sub
      (add_zero (-1 : ℤ) ▸ f.isHomogeneous_barMap.comp
        (isHomogeneous_vogtBarHA V.isHomogeneous_ξ))).sub
      (((by decide : (-2 : ℤ) + 1 = -1) ▸ BB.isHomogeneous_barDifferential.comp hM).sub
        ((by decide : (1 : ℤ) + -2 = -1) ▸ hM.comp AA.isHomogeneous_barDifferential)))
private theorem isHomogeneous_deltaXi {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaXi hA') (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece (-1) :=
  let hHA := isHomogeneous_vogtBarHA V.isHomogeneous_ξ
  let hQ := add_zero (0 : ℤ) ▸ (isHomogeneous_letter (AA.grading.shift 1)).comp
    (((g.comp f).isHomogeneous_barMap.sub (LinearMap.isHomogeneous_id _)).sub
      ((neg_add_cancel (1 : ℤ) ▸ AA.isHomogeneous_barDifferential.comp hHA).add
        (add_neg_cancel (1 : ℤ) ▸ hHA.comp AA.isHomogeneous_barDifferential)))
  (add_zero (-1 : ℤ) ▸ ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2
      g.isHomogeneous_linearPart).comp V.isHomogeneous_topS).sub
    (zero_add (-1 : ℤ) ▸ ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA').comp hQ)
private theorem isHomogeneous_deltaMu {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaMu hA') (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2) :=
  let hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  let hhA₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA'
  let hhB₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hR.isHomogeneous_linearHomotopy
  let hdξ := V.isHomogeneous_deltaXi hhA'; let h₂ : (-1 : ℤ) + -1 = -2 := by decide
  ((h₂ ▸ hhB₁.comp (V.isHomogeneous_topS.sub (add_zero (-1 : ℤ) ▸ hf₁.comp hdξ))).add
    (add_zero (-2 : ℤ) ▸ hf₁.comp (h₂ ▸ hhA₁.comp hdξ))).neg
private theorem deltaXi_eq_zero (hA' : A →ₗ[R] A) {w} (hw : w ∈ filtration R A k) :
    V.deltaXi hA' w = 0 := by
  simp only [deltaXi, LinearMap.sub_apply, LinearMap.comp_apply, V.topQ_eq_zero hw,
    V.topS_eq_zero hw, map_zero, sub_self]
private theorem deltaMu_eq_zero (hA' : A →ₗ[R] A) {w} (hw : w ∈ filtration R A k) :
    V.deltaMu hA' w = 0 := by
  simp only [deltaMu, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, V.topS_eq_zero hw, V.deltaXi_eq_zero hA' hw, map_zero, sub_zero,
    add_zero, neg_zero]
private theorem vogtBarHA_deltaXi (hA' : A →ₗ[R] A) {u} (hu : u ∈ filtration R A (k + 1)) :
    vogtBarHA f g (V.deltaXi hA') u = ofLetter R A (V.deltaXi hA' u) :=
  gradedCoderivAlong_eq_ofLetter_of_mem_filtration _ 1 (g.comp f).isCoalgHom_barMap
    (isCoalgHom_id A) (fun _ ↦ V.deltaXi_eq_zero hA') hu

section StepUpdate
variable {hA' : A →ₗ[R] A}
  (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
    AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential)
include hhA'_eq

private theorem differential_deltaXi_add {z} (hz : z ∈ filtration R A (k + 1)) :
    AA.differential (V.deltaXi hA' z) + V.deltaXi hA' (AA.unaryBarDifferential z) = V.topQ z := by
  have hsz := congrArg g.linearPart (V.topS_diff_eq hz)
  have hg₁ := LinearMap.congr_fun g.differential_comp_linearPart (V.topS z)
  have hAz := LinearMap.congr_fun hhA'_eq (V.topQ z)
  simp only [deltaXi, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub, map_add] at hg₁ hAz hsz ⊢
  rw [← hg₁] at hsz; rw [V.topQ_closed hz] at hAz
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hsz hAz)))
private theorem differential_deltaMu_sub {z} (hz : z ∈ filtration R A (k + 1)) :
    BB.differential (V.deltaMu hA' z) - V.deltaMu hA' (AA.unaryBarDifferential z) =
      V.topS z - f.linearPart (V.deltaXi hA' z) := by
  set dξ := V.deltaXi hA' with hdξ_def; set s' := V.topS - f.linearPart ∘ₗ dξ with hs'_def
  have hdξ := V.differential_deltaXi_add hhA'_eq hz
  have hs'_anti : s' (AA.unaryBarDifferential z) = -BB.differential (s' z) := by
    have hxz := congrArg f.linearPart hdξ
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (dξ z)
    simp only [hs'_def, hdξ_def, LinearMap.sub_apply, LinearMap.comp_apply,
      map_sub, map_add] at hxz hf₁ ⊢
    rw [← hf₁] at hxz
    exact sub_eq_zero.1 (Eq.trans (by abel)
      (sub_eq_zero.2 (congrArg₂ (· + ·) (V.topS_diff_eq hz) hxz.symm)))
  have hgz : f.linearPart (g.linearPart (s' z)) =
      f.linearPart (hA' (dξ (AA.unaryBarDifferential z))) -
        BB.differential (f.linearPart (hA' (dξ z))) := by
    have hAz := LinearMap.congr_fun hhA'_eq (dξ z)
    rw [← LinearMap.comp_apply (f := BB.differential), f.differential_comp_linearPart,
      LinearMap.comp_apply, ← map_sub]
    refine congrArg f.linearPart ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hAz
    simp only [hs'_def, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    have htop : g.linearPart (V.topS z) = dξ z + hA' (V.topQ z) := eq_add_of_sub_eq
      (by simp only [hdξ_def, deltaXi, LinearMap.sub_apply, LinearMap.comp_apply])
    rw [htop, ← hdξ, map_add, hdξ_def]
    rw [hdξ_def] at hAz; exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 hAz.symm))
  have hBz := LinearMap.congr_fun (linearPart_right_eq hR) (s' z)
  rw [deltaMu, ← hdξ_def, ← hs'_def, ← LinearMap.comp_apply f.linearPart, ← LinearMap.sub_apply,
    ← hs'_def]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_neg, map_add, hs'_anti] at hBz ⊢
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hBz hgz.symm)))
private theorem next_vanishes_Q {z} (hz : z ∈ filtration R A (k + 1)) :
    vogtErrQ f g (V.ξ + V.deltaXi hA') z = 0 := by
  have hhi := AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have heq : vogtErrQ f g (V.ξ + V.deltaXi hA') z = V.errQ z - (AA.barDifferential
      (vogtBarHA f g (V.deltaXi hA') z) + vogtBarHA f g (V.deltaXi hA') (AA.barDifferential z)) :=
    by simp only [vogtErrQ, vogtBarHA, gradedCoderivAlong_add, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add]; abel
  rw [heq, V.errQ_apply_ofLetter hz, V.vogtBarHA_deltaXi hA' hz,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    V.vogtBarHA_deltaXi hA' (filtration_monotone R A k.le_succ hhi),
    V.deltaXi_eq_zero hA' hhi, map_zero, add_zero,
    V.vogtBarHA_deltaXi hA' (AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    ← map_add, ← map_sub, V.differential_deltaXi_add hhA'_eq hz, sub_self, map_zero]
private theorem next_vanishes_S {z} (hz : z ∈ filtration R A (k + 1)) :
    vogtErrS hR (V.ξ + V.deltaXi hA') (V.μ + V.deltaMu hA') z = 0 := by
  have hM {u} (hu : u ∈ filtration R A (k + 1)) := gradedCoderivAlong_eq_ofLetter_of_mem_filtration
    (AA.grading.shift 1) 0 (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap)
    f.isCoalgHom_barMap (fun _ ↦ V.deltaMu_eq_zero hA') hu
  have hhi := AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have heq : vogtErrS hR (V.ξ + V.deltaXi hA') (V.μ + V.deltaMu hA') z = V.errS z -
      f.barMap (vogtBarHA f g (V.deltaXi hA') z) - (BB.barDifferential
        (vogtBarM f g (V.deltaMu hA') z) - vogtBarM f g (V.deltaMu hA') (AA.barDifferential z)) :=
    by simp only [vogtErrS, vogtBarHA, vogtBarM, gradedCoderivAlong_add, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add]; abel
  rw [heq, V.errS_apply_ofLetter hz, V.vogtBarHA_deltaXi hA' hz, f.barMap_ofLetter, hM hz,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    hM (filtration_monotone R A k.le_succ hhi), V.deltaMu_eq_zero hA' hhi,
    map_zero, add_zero, hM (AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩), ← map_sub,
    ← map_sub, ← map_sub, V.differential_deltaMu_sub hhA'_eq hz, sub_self, map_zero]
end StepUpdate
end VogtStep

section VogtSeq
variable {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
  (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
  (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
  (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
    AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
include hhA hhA_eq

private noncomputable def vogtBase : VogtStep hR 1 where
  ξ := adjointHomotopy f g hR.linearHomotopy hA ∘ₗ letter R A
  μ := vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ letter R A
  isHomogeneous_ξ := zero_add (-1 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2
    (isHomogeneous_adjointHomotopy hR hhA)).comp (isHomogeneous_letter (AA.grading.shift 1))
  isHomogeneous_μ := zero_add (-2 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2
    (isHomogeneous_vogtTwoHomotopy hR hhA)).comp (isHomogeneous_letter (AA.grading.shift 1))
  vanishes_Q w hw := apply_eq_zero_of_mem_filtration_one R A (LinearMap.ext fun a ↦ by
    have ha := congrArg (ofLetter R A) (LinearMap.congr_fun (adjointHomotopy_chain_eq hR hhA_eq) a)
    simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, barMap_comp, f.barMap_ofLetter, g.barMap_ofLetter,
      gradedCoderivAlong_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, map_sub, map_add] at ha ⊢; exact sub_eq_zero.2 ha) w hw
  vanishes_S w hw := apply_eq_zero_of_mem_filtration_one R A (LinearMap.ext fun a ↦ by
    have ha := congrArg (ofLetter R B) (LinearMap.congr_fun (vogtTwoHomotopy_diff_eq hR hhA_eq) a)
    simp only [vogtErrS, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      f.barMap_ofLetter, hR.barHomotopy_ofLetter, gradedCoderivAlong_ofLetter, letter_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      map_sub] at ha ⊢; exact sub_eq_zero.2 ha.symm) w hw
private noncomputable def vogtSeq : (k : ℕ) → VogtStep hR (k + 1)
  | 0 => vogtBase hR hhA hhA_eq
  | k + 1 =>
      let v := vogtSeq k; let hA' := adjointHomotopy f g hR.linearHomotopy hA
      let hh := isHomogeneous_adjointHomotopy hR hhA; let heq := adjointHomotopy_chain_eq hR hhA_eq
      ⟨v.ξ + v.deltaXi hA', v.μ + v.deltaMu hA', v.isHomogeneous_ξ.add (v.isHomogeneous_deltaXi hh),
        v.isHomogeneous_μ.add (v.isHomogeneous_deltaMu hh), fun _ ↦ v.next_vanishes_Q heq,
        fun _ ↦ v.next_vanishes_S heq⟩
private theorem vogtSeq_ξ_stab (k : ℕ) : ∀ w ∈ filtration R A k,
    (vogtSeq hR hhA hhA_eq (k + 1)).ξ w = (vogtSeq hR hhA hhA_eq k).ξ w := fun _ hw ↦ by
  simp only [vogtSeq, LinearMap.add_apply,
    (vogtSeq hR hhA hhA_eq k).deltaXi_eq_zero _ (filtration_monotone R A k.le_succ hw), add_zero]
end VogtSeq

public section
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
      have hH {w} (hw : w ∈ filtration R A n) := gradedCoderivAlong_stabilisingLinearMap_apply
        (G := AA.grading.shift 1) (q := 1) (φ := fun k ↦ (seq k).ξ) (g.comp f).isCoalgHom_barMap
        (AInfinityHom.id AA).isCoalgHom_barMap (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)
        (vogtSeq_ξ_stab hR hhA hhA_eq) (fun _ _ ↦ rfl) (fun _ _ ↦ by rw [barMap_id]) hw
      have heq := (seq n).vanishes_Q z (filtration_monotone R A n.le_succ hn)
      simp only [vogtErrQ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at heq ⊢
      rw [hH hn, hH (AA.barDifferential_mem_filtration hn), barMap_id]; exact sub_eq_zero.1 heq }

namespace LinearHomotopyInverse
variable {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f)

/-- The left `A∞` homotopy from `L.homotopyInverse.comp f` to `AInfinityHom.id AA`. -/
noncomputable def homotopyHomotopyInverseComp :
    Homotopy (L.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  homotopyOfRightHomotopy f L.homotopyInverse L.homotopyCompHomotopyInverse
    L.isHomogeneous_homotopyLeft (L.linearPart_homotopyInverse.symm ▸ L.inv_comp_linearPart_sub_id)

/-- Bundled two-sided `A∞` homotopy equivalence associated to `LinearHomotopyInverse f`. -/
noncomputable def homotopyEquiv : HomotopyEquiv AA BB :=
  ⟨f, L.homotopyInverse, L.homotopyHomotopyInverseComp, L.homotopyCompHomotopyInverse⟩

@[simp] theorem homotopyEquiv_hom : L.homotopyEquiv.hom = f := (rfl)
@[simp] theorem homotopyEquiv_inv : L.homotopyEquiv.inv = L.homotopyInverse := (rfl)
@[simp] theorem barHomotopy_homotopyEquiv_homotopyInvCompHom :
    L.homotopyEquiv.homotopyInvCompHom.barHomotopy = L.homotopyHomotopyInverseComp.barHomotopy :=
  (rfl)
@[simp] theorem barHomotopy_homotopyEquiv_homotopyHomCompInv :
    L.homotopyEquiv.homotopyHomCompInv.barHomotopy = L.homotopyCompHomotopyInverse.barHomotopy :=
  (rfl)
end LinearHomotopyInverse
end
end Vogt

public section
namespace HomotopyEquiv
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
  (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC)

/-- Transitivity of `A∞` homotopy equivalences, with forward morphism `e₂.hom.comp e₁.hom`. -/
noncomputable def trans : HomotopyEquiv AA CC :=
  (e₂.linearHomotopyInverse.comp e₁.linearHomotopyInverse).homotopyEquiv

@[simp] theorem trans_hom : (e₁.trans e₂).hom = e₂.hom.comp e₁.hom := (rfl)
@[simp] theorem linearPart_trans_inv :
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

/-- Unfolding characterization of `AInfinityHom.IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) : f.IsHomotopyEquiv ↔
    ∃ g : AInfinityHom BB AA, Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) := Iff.rfl

/-- The forward morphism of a `HomotopyEquiv` is a homotopy equivalence. -/
theorem HomotopyEquiv.isHomotopyEquiv_hom (e : HomotopyEquiv AA BB) : e.hom.IsHomotopyEquiv :=
  ⟨e.inv, ⟨e.homotopyInvCompHom⟩, ⟨e.homotopyHomCompInv⟩⟩

/-- The inverse morphism of a `HomotopyEquiv` is a homotopy equivalence. -/
theorem HomotopyEquiv.isHomotopyEquiv_inv (e : HomotopyEquiv AA BB) : e.inv.IsHomotopyEquiv :=
  ⟨e.hom, ⟨e.homotopyHomCompInv⟩, ⟨e.homotopyInvCompHom⟩⟩

/-- **Over any commutative ring, an `A∞` morphism is a homotopy equivalence if and only if its
linear part admits a homogeneous chain-homotopy inverse.** -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f) :=
  ⟨fun ⟨g, ⟨hL⟩, ⟨hR⟩⟩ ↦ ⟨(HomotopyEquiv.mk f g hL hR).linearHomotopyInverse⟩,
    fun ⟨L⟩ ↦ L.homotopyEquiv.isHomotopyEquiv_hom⟩

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv :=
  let ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf; ⟨g, ⟨Homotopy.ofEq hg₁⟩, ⟨Homotopy.ofEq hg₂⟩⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso :=
  let ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf; (HomotopyEquiv.mk f g hL hR).isQuasiIso_hom

/-- Being an `A∞` homotopy equivalence is invariant under `A∞` homotopy. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  simp only [isHomotopyEquiv_iff_nonempty_linearHomotopyInverse]
  exact ⟨fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverse L⟩, fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverseSymm L⟩⟩

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp] theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, ⟨Homotopy.ofEq (comp_id _)⟩, ⟨Homotopy.ofEq (comp_id _)⟩⟩

/-- The composition of two `A∞` homotopy equivalences is a homotopy equivalence. -/
theorem IsHomotopyEquiv.comp {C : Type uC} [AddCommGroup C] [Module R C]
    {CC : AInfinityAlgebra R C} {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv :=
  let ⟨Lg⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse g).1 hg
  let ⟨Lf⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse f).1 hf
  (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse _).2 ⟨Lg.comp Lf⟩
end IsHomotopyEquiv
end
end AInfinityHom
end TauCeti
