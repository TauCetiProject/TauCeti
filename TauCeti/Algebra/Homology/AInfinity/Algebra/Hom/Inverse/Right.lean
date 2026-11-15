/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.RelativeCoderivation
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
import Mathlib.Tactic.Abel

/-!
# Simultaneous arity-by-arity construction of right A-infinity homotopy inverses

Given homogeneous chain-homotopy inverse data `L : LinearHomotopyInverse f` for the linear part of
an `A∞` morphism `f : A ⟶ B` over a commutative ring `R`, this file lifts `L` simultaneously to an
`A∞` morphism `g : B ⟶ A` with linear part `L.inv` and a right `A∞` homotopy `f ∘ g ⇒ id_B` with
linear homotopy `L.homotopyRight`, by induction along the conilpotence filtration of `Tᶜ(sB)`:

* At filtration `k`, `γ_k` generates a coalgebra map `G_k` intertwining `b_B` and `b_A` on
  `filtration k`, and `η_k` generates an `(F ∘ G_k, id)`-coderivation `H_k` bounding `F ∘ G_k - id`
  on `filtration k`.
* On `filtration (k + 1)`, every proper cut lies in `filtration k`, so both the morphism defect
  `E = b_A ∘ G_k - G_k ∘ b_B` and the homotopy residual
  `R_H = (F ∘ G_k - id) - (b_B ∘ H_k + H_k ∘ b_B)` take single-letter values
  (`TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration`).
* The top-arity projections `e` and `r` satisfy `d_A ∘ e + e ∘ b₁ = 0` and
  `d_B ∘ r - r ∘ b₁ = f₁ ∘ e`.  Adding `δ = h_A ∘ e - g₁ ∘ r` to `γ_k` and
  `ν = f₁ ∘ h_A ∘ δ - h_B ∘ (r + f₁ ∘ δ)` to `η_k` cancels both defects on `filtration (k + 1)`
  without altering `filtration k`, and passing to the stabilising limit produces
  `L.homotopyInverse` and `L.homotopyCompHomotopyInverse`.

## Main definitions

* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyInverse`: the `A∞` morphism `B ⟶ A` lifted
  from `LinearHomotopyInverse f`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyCompHomotopyInverse`: the right `A∞` homotopy
  `Homotopy (f.comp L.homotopyInverse) (AInfinityHom.id BB)`.

## Main results

* `TauCeti.AInfinityHom.LinearHomotopyInverse.linearPart_homotopyInverse`: the linear part of
  `L.homotopyInverse` is `L.inv`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.linearHomotopy_homotopyCompHomotopyInverse`: the
  linear homotopy of `L.homotopyCompHomotopyInverse` is `L.homotopyRight`.

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Theorem 1.3.1.2.
* M. Markl, *Transferring A-infinity (strongly homotopy associative) structures*, Rend. Circ. Mat.
  Palermo (2) Suppl. 79 (2006), 139--151.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {f : AInfinityHom AA BB}

/-- Inductive state at filtration level `k` for the simultaneous construction of a right `A∞`
homotopy inverse `G_k` and right bar homotopy `H_k`. -/
private structure RightInvStep (L : LinearHomotopyInverse f) (k : ℕ) where
  γ : ReducedTensorWords R B →ₗ[R] A
  η : ReducedTensorWords R B →ₗ[R] B
  isHomogeneous_γ :
    LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  isHomogeneous_η :
    LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  intertwines : ∀ w ∈ filtration R B k,
    AA.barDifferential (coalgHom R γ w) = coalgHom R γ (BB.barDifferential w)
  homotopy_eq : ∀ w ∈ filtration R B k,
    ((f.barMap ∘ₗ coalgHom R γ - (LinearMap.id : ReducedTensorWords R B →ₗ[R] _)) -
      (BB.barDifferential ∘ₗ
          gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R γ)
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) η +
        gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R γ)
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) η ∘ₗ
          BB.barDifferential)) w = 0

namespace RightInvStep

variable {L : LinearHomotopyInverse f} {k : ℕ}

private noncomputable def barG (S : RightInvStep L k) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  coalgHom R S.γ

private noncomputable def barH (S : RightInvStep L k) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ S.barG)
    (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) S.η

private noncomputable def errG (S : RightInvStep L k) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ S.barG - S.barG ∘ₗ BB.barDifferential

private noncomputable def errH (S : RightInvStep L k) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  (f.barMap ∘ₗ S.barG - (LinearMap.id : ReducedTensorWords R B →ₗ[R] _)) -
    (BB.barDifferential ∘ₗ S.barH + S.barH ∘ₗ BB.barDifferential)

private noncomputable def obsE (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] A :=
  (letter R A ∘ₗ S.errG) ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩

private noncomputable def obsR (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] B :=
  (letter R B ∘ₗ S.errH) ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩

private noncomputable def delta (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] A :=
  L.homotopyLeft ∘ₗ S.obsE - L.inv ∘ₗ S.obsR

private noncomputable def nu (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] B :=
  f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta -
    L.homotopyRight ∘ₗ (S.obsR + f.linearPart ∘ₗ S.delta)

private theorem isHomogeneous_barG (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.barG (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 :=
  isHomogeneous_coalgHom S.isHomogeneous_γ

private theorem isHomogeneous_barH (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.barH (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
  have hFG : LinearMap.IsHomogeneous (f.barMap ∘ₗ S.barG) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp S.isHomogeneous_barG
  have hlFG : LinearMap.IsHomogeneous (letter R B ∘ₗ (f.barMap ∘ₗ S.barG))
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
    simpa only [add_zero] using (isHomogeneous_letter (BB.grading.shift 1)).comp hFG
  exact isHomogeneous_gradedCoderivAlong hlFG (LinearMap.isHomogeneous_id _) S.isHomogeneous_η

private theorem isHomogeneous_obsE (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.obsE (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
  have hE₁ : LinearMap.IsHomogeneous (AA.barDifferential ∘ₗ S.barG)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp S.isHomogeneous_barG
  have hE₂ : LinearMap.IsHomogeneous (S.barG ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [add_zero] using S.isHomogeneous_barG.comp BB.isHomogeneous_barDifferential
  have hlE : LinearMap.IsHomogeneous (letter R A ∘ₗ S.errG) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
    simpa only [errG, add_zero] using
      (isHomogeneous_letter (AA.grading.shift 1)).comp (hE₁.sub hE₂)
  simpa only [obsE, zero_add] using hlE.comp (isHomogeneous_lengthProj (BB.grading.shift 1) _)

private theorem isHomogeneous_obsR (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.obsR (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
  have hFG₁ : LinearMap.IsHomogeneous (f.barMap ∘ₗ S.barG)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp S.isHomogeneous_barG
  have hHb₁ : LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ S.barH)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp S.isHomogeneous_barH
  have hHb₂ : LinearMap.IsHomogeneous (S.barH ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_neg_cancel] using S.isHomogeneous_barH.comp BB.isHomogeneous_barDifferential
  have herrH := (hFG₁.sub (LinearMap.isHomogeneous_id _)).sub (hHb₁.add hHb₂)
  have hlR : LinearMap.IsHomogeneous (letter R B ∘ₗ S.errH) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [errH, add_zero] using (isHomogeneous_letter (BB.grading.shift 1)).comp herrH
  simpa only [obsR, add_zero] using hlR.comp (isHomogeneous_lengthProj (BB.grading.shift 1) _)

private theorem isHomogeneous_delta (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.delta (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  have h₁ : LinearMap.IsHomogeneous (L.homotopyLeft ∘ₗ S.obsE)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa only [add_neg_cancel] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_homotopyLeft).comp
        S.isHomogeneous_obsE
  have h₂ : LinearMap.IsHomogeneous (L.inv ∘ₗ S.obsR)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_inv).comp S.isHomogeneous_obsR
  exact h₁.sub h₂

private theorem isHomogeneous_nu (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.nu (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyLeft
  have hhB := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyRight
  have h₁ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa only [zero_add, add_zero] using hf₁.comp (hhA.comp S.isHomogeneous_delta)
  have hfδ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ S.delta)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
    simpa only [add_zero] using hf₁.comp S.isHomogeneous_delta
  have h₂ : LinearMap.IsHomogeneous (L.homotopyRight ∘ₗ (S.obsR + f.linearPart ∘ₗ S.delta))
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa only [zero_add] using hhB.comp (S.isHomogeneous_obsR.add hfδ)
  exact h₁.sub h₂

private theorem errG_eq_zero_of_mem_filtration (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.errG w = 0 :=
  sub_eq_zero.2 (S.intertwines w hw)

private theorem errG_apply_ofLetter (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) : S.errG z = ofLetter R A (S.obsE z) := by
  have hcod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 S.barG S.barG S.errG :=
    (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom (isCoalgHom_coalgHom _)
      S.isHomogeneous_barG).sub
      ((isCoalgHom_coalgHom _).comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential)
  have hl : ∀ w ∈ filtration R B k, (letter R A ∘ₗ S.errG) w = 0 := fun w hw ↦ by
    rw [LinearMap.comp_apply, S.errG_eq_zero_of_mem_filtration hw, map_zero]
  rw [obsE, LinearMap.comp_apply, apply_lengthProj_of_mem_filtration R B hl hz]
  exact hcod.apply_eq_ofLetter_of_mem_filtration hl hz

private theorem obsE_cocycle (S : RightInvStep L k) :
    AA.differential ∘ₗ S.obsE + S.obsE ∘ₗ BB.unaryBarDifferential = 0 := by
  refine LinearMap.ext fun w ↦ ?_
  set p := lengthProj R B ⟨k + 1, k.succ_pos⟩
  have hpz : p w ∈ filtration R B (k + 1) :=
    lengthProj_mem_filtration R B ⟨k + 1, k.succ_pos⟩ w
  have hbE : AA.barDifferential (S.errG (p w)) + S.errG (BB.barDifferential (p w)) = 0 := by
    have hAA := LinearMap.congr_fun AA.barDifferential_sq (S.barG (p w))
    have hBB := LinearMap.congr_fun BB.barDifferential_sq (p w)
    simp only [errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_sub]
      at hAA hBB ⊢
    rw [hAA, hBB, map_zero]
    abel
  have hhi : S.errG (BB.higherBarDifferential (p w)) = 0 :=
    S.errG_eq_zero_of_mem_filtration (BB.higherBarDifferential_filtration k ⟨p w, hpz, rfl⟩)
  have hun : BB.unaryBarDifferential (p w) ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨p w, hpz, rfl⟩
  rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hhi, add_zero,
    S.errG_apply_ofLetter hpz, S.errG_apply_ofLetter hun, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, ← map_add] at hbE
  have hl := congrArg (letter R A) hbE
  rw [letter_ofLetter, map_zero] at hl
  have hpE : S.obsE (p w) = S.obsE w := by
    simp only [obsE, p, LinearMap.comp_apply, lengthProj_lengthProj]
  have hpU : S.obsE (BB.unaryBarDifferential (p w)) = S.obsE (BB.unaryBarDifferential w) := by
    have hc := LinearMap.congr_fun (BB.lengthProj_comp_unaryBarDifferential ⟨k + 1, k.succ_pos⟩) w
    simp only [LinearMap.comp_apply] at hc
    simp only [obsE, p, LinearMap.comp_apply, ← hc, lengthProj_lengthProj]
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, hpE, hpU] using hl

private theorem errH_apply_ofLetter (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) : S.errH z = ofLetter R B (S.obsR z) := by
  have hFc : IsCoalgHom R (f.barMap ∘ₗ S.barG) :=
    f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)
  have hD : IsGradedCoderivationAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ S.barG) LinearMap.id
      S.barH :=
    isGradedCoderivationAlong_gradedCoderivAlong _ 1 hFc (isCoalgHom_id (R := R) B) S.η
  have hFG₀ : LinearMap.IsHomogeneous (f.barMap ∘ₗ S.barG) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp S.isHomogeneous_barG
  have hFGb : ∀ w ∈ filtration R B k,
      BB.barDifferential ((f.barMap ∘ₗ S.barG) w) = (f.barMap ∘ₗ S.barG) (BB.barDifferential w) :=
    fun w hw ↦ by
      simp only [barG, LinearMap.comp_apply, f.barDifferential_barMap, S.intertwines w hw]
  have hprim := hD.sub_comp_add_comp_of_mem_filtration S.isHomogeneous_barH (by decide)
    BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFc (isCoalgHom_id (R := R) B) hFG₀ hFGb (fun _ _ ↦ rfl)
    (fun w hw ↦ by simpa only [barG, barH] using S.homotopy_eq w hw) hz
  have hl : ∀ w ∈ filtration R B k, (letter R B ∘ₗ S.errH) w = 0 := fun w hw ↦ by
    rw [LinearMap.comp_apply, errH, barH, barG, S.homotopy_eq w hw, map_zero]
  rw [obsR, LinearMap.comp_apply, apply_lengthProj_of_mem_filtration R B hl hz]
  exact hprim

private theorem obsR_diff_eq (S : RightInvStep L k) :
    BB.differential ∘ₗ S.obsR - S.obsR ∘ₗ BB.unaryBarDifferential = f.linearPart ∘ₗ S.obsE := by
  refine LinearMap.ext fun w ↦ ?_
  set p := lengthProj R B ⟨k + 1, k.succ_pos⟩
  have hpz : p w ∈ filtration R B (k + 1) :=
    lengthProj_mem_filtration R B ⟨k + 1, k.succ_pos⟩ w
  have hbR : BB.barDifferential (S.errH (p w)) - S.errH (BB.barDifferential (p w)) =
      f.barMap (S.errG (p w)) := by
    have h₁ := LinearMap.congr_fun BB.barDifferential_sq (S.barH (p w))
    have h₂ := LinearMap.congr_fun BB.barDifferential_sq (p w)
    simp only [errH, errG, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂, map_zero, f.barDifferential_barMap]
    abel
  have hhi : S.errH (BB.higherBarDifferential (p w)) = 0 := by
    rw [errH, barH, barG]
    exact S.homotopy_eq _ (BB.higherBarDifferential_filtration k ⟨p w, hpz, rfl⟩)
  have hun : BB.unaryBarDifferential (p w) ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨p w, hpz, rfl⟩
  nth_rw 2 [BB.barDifferential_eq_unary_add_higher] at hbR
  rw [LinearMap.add_apply, map_add, hhi, add_zero,
    S.errH_apply_ofLetter hpz, S.errH_apply_ofLetter hun, S.errG_apply_ofLetter hpz,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    f.barMap_ofLetter, ← map_sub] at hbR
  have hl := congrArg (letter R B) hbR
  rw [letter_ofLetter, letter_ofLetter] at hl
  have hpR : S.obsR (p w) = S.obsR w := by
    simp only [obsR, p, LinearMap.comp_apply, lengthProj_lengthProj]
  have hpE : S.obsE (p w) = S.obsE w := by
    simp only [obsE, p, LinearMap.comp_apply, lengthProj_lengthProj]
  have hpU : S.obsR (BB.unaryBarDifferential (p w)) = S.obsR (BB.unaryBarDifferential w) := by
    have hc := LinearMap.congr_fun (BB.lengthProj_comp_unaryBarDifferential ⟨k + 1, k.succ_pos⟩) w
    simp only [LinearMap.comp_apply] at hc
    simp only [obsR, p, LinearMap.comp_apply, ← hc, lengthProj_lengthProj]
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, hpR, hpE, hpU] using hl

private theorem differential_delta_sub (S : RightInvStep L k) :
    AA.differential ∘ₗ S.delta - S.delta ∘ₗ BB.unaryBarDifferential = -S.obsE := by
  have he : S.obsE ∘ₗ BB.unaryBarDifferential = -(AA.differential ∘ₗ S.obsE) :=
    eq_neg_of_add_eq_zero_right S.obsE_cocycle
  have hr := S.obsR_diff_eq
  calc
    AA.differential ∘ₗ S.delta - S.delta ∘ₗ BB.unaryBarDifferential
      = AA.differential ∘ₗ L.homotopyLeft ∘ₗ S.obsE -
          L.homotopyLeft ∘ₗ (S.obsE ∘ₗ BB.unaryBarDifferential) -
          L.inv ∘ₗ (BB.differential ∘ₗ S.obsR - S.obsR ∘ₗ BB.unaryBarDifferential) := by
        refine LinearMap.ext fun z ↦ ?_
        have hinv := LinearMap.congr_fun L.differential_comp_inv (S.obsR z)
        simp only [delta, LinearMap.sub_apply, LinearMap.comp_apply] at hinv ⊢
        rw [map_sub, map_sub, hinv]
        abel
    _ = (AA.differential ∘ₗ L.homotopyLeft + L.homotopyLeft ∘ₗ AA.differential) ∘ₗ S.obsE -
          L.inv ∘ₗ f.linearPart ∘ₗ S.obsE := by
        rw [he, hr]
        refine LinearMap.ext fun z ↦ ?_
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
          LinearMap.comp_apply, map_neg]
        abel
    _ = -S.obsE := by
        rw [← L.inv_comp_linearPart_sub_id]
        refine LinearMap.ext fun z ↦ ?_
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
          LinearMap.neg_apply]
        abel

private theorem differential_nu_add (S : RightInvStep L k) :
    BB.differential ∘ₗ S.nu + S.nu ∘ₗ BB.unaryBarDifferential =
      S.obsR + f.linearPart ∘ₗ S.delta := by
  set r' := S.obsR + f.linearPart ∘ₗ S.delta
  have hd : S.obsE = S.delta ∘ₗ BB.unaryBarDifferential - AA.differential ∘ₗ S.delta := by
    rw [← neg_sub, S.differential_delta_sub, neg_neg]
  have hr'_closed : r' ∘ₗ BB.unaryBarDifferential = BB.differential ∘ₗ r' := by
    refine LinearMap.ext fun z ↦ ?_
    have hz₁ := LinearMap.congr_fun S.obsR_diff_eq z
    have hdz := LinearMap.congr_fun hd z
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (S.delta z)
    simp only [r', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
      at hz₁ hdz hf₁ ⊢
    rw [sub_eq_iff_eq_add.1 hz₁, hdz, map_sub, ← hf₁]
    abel
  have hgr' : f.linearPart ∘ₗ L.inv ∘ₗ r' =
      BB.differential ∘ₗ (f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta) +
        (f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta) ∘ₗ BB.unaryBarDifferential := by
    have hg : L.inv ∘ₗ r' = L.homotopyLeft ∘ₗ S.obsE + (L.inv ∘ₗ f.linearPart - LinearMap.id) ∘ₗ
        S.delta := by
      refine LinearMap.ext fun z ↦ ?_
      simp only [r', delta, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_add]
      abel
    rw [hg, L.inv_comp_linearPart_sub_id, hd]
    refine LinearMap.ext fun z ↦ ?_
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (L.homotopyLeft (S.delta z))
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub]
      at hf₁ ⊢
    rw [← hf₁]
    abel
  refine LinearMap.ext fun z ↦ ?_
  have hB := LinearMap.congr_fun L.linearPart_comp_inv_sub_id (r' z)
  have hrc := LinearMap.congr_fun hr'_closed z
  have hgz := LinearMap.congr_fun hgr' z
  simp only [nu, r', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub] at hB hrc hgz ⊢
  rw [hrc]
  refine sub_eq_zero.1 (Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hgz.symm hB)))
  abel

private theorem delta_eq_zero_of_mem_filtration (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.delta w = 0 := by
  have hp := lengthProj_apply_eq_zero_of_mem_filtration R B (n := ⟨k + 1, k.succ_pos⟩)
    (Nat.lt_succ_self k) hw
  simp only [delta, obsE, obsR, LinearMap.sub_apply, LinearMap.comp_apply, hp, map_zero, sub_self]

private theorem nu_eq_zero_of_mem_filtration (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.nu w = 0 := by
  have hp := lengthProj_apply_eq_zero_of_mem_filtration R B (n := ⟨k + 1, k.succ_pos⟩)
    (Nat.lt_succ_self k) hw
  have hd := S.delta_eq_zero_of_mem_filtration hw
  simp only [nu, obsR, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hp, hd,
    map_zero, add_zero, sub_self]

private theorem coalgHom_add_delta_eq (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : coalgHom R (S.γ + S.delta) w = S.barG w :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun u hu ↦ by
      simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        LinearMap.add_apply, S.delta_eq_zero_of_mem_filtration hu, add_zero]) hw

private theorem coalgHom_add_delta_filtration_succ (S : RightInvStep L k)
    {u : ReducedTensorWords R B} (hu : u ∈ filtration R B (k + 1)) :
    coalgHom R (S.γ + S.delta) u = S.barG u + ofLetter R A (S.delta u) :=
  eq_add_of_sub_eq' <|
    (isCoalgHom_coalgHom _).sub_apply_eq_ofLetter_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ congrArg (letter R A) (S.coalgHom_add_delta_eq hw)) hu
      |>.trans (by
        simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          LinearMap.add_apply, add_sub_cancel_left])

private theorem next_intertwines (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    AA.barDifferential (coalgHom R (S.γ + S.delta) z) =
      coalgHom R (S.γ + S.delta) (BB.barDifferential z) := by
  have hhi : BB.higherBarDifferential z ∈ filtration R B k :=
    BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hun : BB.unaryBarDifferential z ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, S.coalgHom_add_delta_filtration_succ hun,
    S.coalgHom_add_delta_eq hhi]
  have hE := S.errG_apply_ofLetter hz
  rw [errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add] at hE
  have hd := congrArg (ofLetter R A) (LinearMap.congr_fun S.differential_delta_sub z)
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply, map_sub, map_neg]
    at hd
  refine sub_eq_zero.1 (Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hE hd)))
  abel

private theorem next_homotopy_eq (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    ((f.barMap ∘ₗ coalgHom R (S.γ + S.delta) -
        (LinearMap.id : ReducedTensorWords R B →ₗ[R] _)) -
      (BB.barDifferential ∘ₗ
          gradedCoderivAlong (BB.grading.shift 1) 1
            (f.barMap ∘ₗ coalgHom R (S.γ + S.delta))
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) (S.η + S.nu) +
        gradedCoderivAlong (BB.grading.shift 1) 1
            (f.barMap ∘ₗ coalgHom R (S.γ + S.delta))
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) (S.η + S.nu) ∘ₗ
          BB.barDifferential)) z = 0 := by
  set G' := coalgHom R (S.γ + S.delta)
  set H' := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G')
    (LinearMap.id : ReducedTensorWords R B →ₗ[R] _) (S.η + S.nu)
  have hH'c := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S.γ + S.delta)))
    (isCoalgHom_id (R := R) B) (S.η + S.nu)
  have hHc := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.γ)) (isCoalgHom_id (R := R) B) S.η
  have hFG_eq : ∀ w ∈ filtration R B k, (f.barMap ∘ₗ G') w = (f.barMap ∘ₗ S.barG) w :=
    fun w hw ↦ by simp only [G', LinearMap.comp_apply, S.coalgHom_add_delta_eq hw]
  have hl_eq : ∀ w ∈ filtration R B k, letter R B (H' w) = letter R B (S.barH w) := fun w hw ↦ by
    simp only [H', barH, ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
      LinearMap.add_apply, S.nu_eq_zero_of_mem_filtration hw, add_zero]
  have hH_eq : ∀ w ∈ filtration R B k, H' w = S.barH w := fun w hw ↦
    hH'c.apply_eq_of_mem_filtration hHc
      (fun u hu ↦ hFG_eq u (filtration_monotone R B (Nat.sub_le k 1) hu))
      (fun _ _ ↦ rfl) hl_eq hw
  have hH_diff : ∀ u ∈ filtration R B (k + 1), H' u = S.barH u + ofLetter R B (S.nu u) :=
    fun u hu ↦ eq_add_of_sub_eq' <|
      hH'c.sub_apply_eq_ofLetter_of_mem_filtration hHc hFG_eq (fun _ _ ↦ rfl) hl_eq hu
        |>.trans (by
          simp only [← LinearMap.comp_apply (letter R B),
            letter_comp_gradedCoderivAlong, LinearMap.add_apply, add_sub_cancel_left])
  have hhi : BB.higherBarDifferential z ∈ filtration R B k :=
    BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hun : BB.unaryBarDifferential z ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  have hR := S.errH_apply_ofLetter hz
  have hν := congrArg (ofLetter R B) (LinearMap.congr_fun S.differential_nu_add z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add] at hν
  simp only [errH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hR ⊢
  rw [BB.barDifferential_eq_unary_add_higher] at hR ⊢
  simp only [LinearMap.add_apply, map_add] at hR ⊢
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, f.barMap_ofLetter, hH_diff z hz, map_add,
    map_add, AInfinityAlgebra.unaryBarDifferential_ofLetter,
    AInfinityAlgebra.higherBarDifferential_ofLetter, add_zero,
    ← AInfinityAlgebra.differential_apply, hH_diff _ hun, hH_eq _ hhi]
  refine Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hR hν.symm))
  abel

/-- Inductive step from filtration `k` to filtration `k + 1`. -/
private noncomputable def next (S : RightInvStep L k) : RightInvStep L (k + 1) where
  γ := S.γ + S.delta
  η := S.η + S.nu
  isHomogeneous_γ := S.isHomogeneous_γ.add S.isHomogeneous_delta
  isHomogeneous_η := S.isHomogeneous_η.add S.isHomogeneous_nu
  intertwines _ hz := S.next_intertwines hz
  homotopy_eq _ hz := S.next_homotopy_eq hz

end RightInvStep

private noncomputable def rightInvBase (L : LinearHomotopyInverse f) : RightInvStep L 1 where
  γ := L.inv ∘ₗ letter R B
  η := L.homotopyRight ∘ₗ letter R B
  isHomogeneous_γ := by
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_inv).comp
        (isHomogeneous_letter (BB.grading.shift 1))
  isHomogeneous_η := by
    simpa only [zero_add] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_homotopyRight).comp
        (isHomogeneous_letter (BB.grading.shift 1))
  intertwines := by
    have h0 : (AA.barDifferential ∘ₗ coalgHom R (L.inv ∘ₗ letter R B) -
        coalgHom R (L.inv ∘ₗ letter R B) ∘ₗ BB.barDifferential) ∘ₗ ofLetter R B = 0 := by
      refine LinearMap.ext fun b ↦ ?_
      have hd := LinearMap.congr_fun L.differential_comp_inv b
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
        coalgHom_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
        ← AInfinityAlgebra.differential_apply] at hd ⊢
      rw [hd, sub_self]
    exact fun w hw ↦ sub_eq_zero.1 (apply_eq_zero_of_mem_filtration_one R B h0 w hw)
  homotopy_eq := by
    apply apply_eq_zero_of_mem_filtration_one R B
    refine LinearMap.ext fun b ↦ ?_
    have hb := congrArg (ofLetter R B) (LinearMap.congr_fun L.linearPart_comp_inv_sub_id b)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, coalgHom_ofLetter, gradedCoderivAlong_ofLetter,
      letter_ofLetter, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, map_sub, map_add] at hb ⊢
    exact sub_eq_zero.2 hb

private noncomputable def rightInvZero (L : LinearHomotopyInverse f) : RightInvStep L 0 where
  γ := L.inv ∘ₗ letter R B
  η := L.homotopyRight ∘ₗ letter R B
  isHomogeneous_γ := (rightInvBase L).isHomogeneous_γ
  isHomogeneous_η := (rightInvBase L).isHomogeneous_η
  intertwines w hw := (rightInvBase L).intertwines w (filtration_monotone R B (Nat.zero_le 1) hw)
  homotopy_eq w hw := (rightInvBase L).homotopy_eq w (filtration_monotone R B (Nat.zero_le 1) hw)

private noncomputable def rightInvSeq (L : LinearHomotopyInverse f) : (k : ℕ) → RightInvStep L k
  | 0 => rightInvZero L
  | 1 => rightInvBase L
  | k + 2 => (rightInvSeq L (k + 1)).next

private theorem rightInvSeq_γ_stabilises (L : LinearHomotopyInverse f) (k : ℕ)
    {w : ReducedTensorWords R B} (hw : w ∈ filtration R B k) :
    (rightInvSeq L (k + 1)).γ w = (rightInvSeq L k).γ w := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [rightInvSeq, RightInvStep.next, LinearMap.add_apply,
        (rightInvSeq L (k + 1)).delta_eq_zero_of_mem_filtration hw, add_zero]

private theorem rightInvSeq_η_stabilises (L : LinearHomotopyInverse f) (k : ℕ)
    {w : ReducedTensorWords R B} (hw : w ∈ filtration R B k) :
    (rightInvSeq L (k + 1)).η w = (rightInvSeq L k).η w := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [rightInvSeq, RightInvStep.next, LinearMap.add_apply,
        (rightInvSeq L (k + 1)).nu_eq_zero_of_mem_filtration hw, add_zero]

private noncomputable def rightInvTaylor (L : LinearHomotopyInverse f) :
    ReducedTensorWords R B →ₗ[R] A :=
  DirectSum.toModule R _ _ fun k ↦ (rightInvSeq L k.1).γ ∘ₗ of R B k

private noncomputable def rightHomotopyTaylor (L : LinearHomotopyInverse f) :
    ReducedTensorWords R B →ₗ[R] B :=
  DirectSum.toModule R _ _ fun k ↦ (rightInvSeq L k.1).η ∘ₗ of R B k

private theorem rightInvTaylor_apply_of_mem_filtration (L : LinearHomotopyInverse f) {n : ℕ}
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B n) :
    rightInvTaylor L z = (rightInvSeq L n).γ z := by
  have hle : ∀ {j m : ℕ}, j ≤ m → ∀ w ∈ filtration R B j,
      (rightInvSeq L m).γ w = (rightInvSeq L j).γ w := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => intro _ _; rfl
    | succ m hjm ih =>
        intro w hw
        rw [rightInvSeq_γ_stabilises L m (filtration_monotone R B hjm hw), ih w hw]
  have heq : filtration R B n ≤ LinearMap.eqLocus (rightInvTaylor L) (rightInvSeq L n).γ := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, rightInvTaylor, toModule_of, LinearMap.comp_apply,
      hle hk _ (of_mem_filtration R B le_rfl x)]
  exact heq hz

private theorem rightHomotopyTaylor_apply_of_mem_filtration (L : LinearHomotopyInverse f) {n : ℕ}
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B n) :
    rightHomotopyTaylor L z = (rightInvSeq L n).η z := by
  have hle : ∀ {j m : ℕ}, j ≤ m → ∀ w ∈ filtration R B j,
      (rightInvSeq L m).η w = (rightInvSeq L j).η w := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => intro _ _; rfl
    | succ m hjm ih =>
        intro w hw
        rw [rightInvSeq_η_stabilises L m (filtration_monotone R B hjm hw), ih w hw]
  have heq : filtration R B n ≤ LinearMap.eqLocus (rightHomotopyTaylor L) (rightInvSeq L n).η := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, rightHomotopyTaylor, toModule_of, LinearMap.comp_apply,
      hle hk _ (of_mem_filtration R B le_rfl x)]
  exact heq hz

private theorem coalgHom_rightInvTaylor_apply_of_mem_filtration (L : LinearHomotopyInverse f)
    {n : ℕ} {z : ReducedTensorWords R B} (hz : z ∈ filtration R B n) :
    coalgHom R (rightInvTaylor L) z = coalgHom R (rightInvSeq L n).γ z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun w hw ↦ by
      simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        rightInvTaylor_apply_of_mem_filtration L hw]) hz

namespace LinearHomotopyInverse

/-- The `A∞` homotopy inverse `BB ⟶ AA` associated to linear chain-homotopy inverse data for
`f.linearPart`. -/
noncomputable def homotopyInverse (L : LinearHomotopyInverse f) : AInfinityHom BB AA where
  barMap := coalgHom R (rightInvTaylor L)
  isCoalgHom_barMap := isCoalgHom_coalgHom _
  isHomogeneous_barMap := isHomogeneous_coalgHom <|
    LinearMap.isHomogeneous_def.2 fun _ z hz ↦ by
      obtain ⟨n, hn⟩ := exists_mem_filtration R B z
      rw [rightInvTaylor_apply_of_mem_filtration L hn]
      exact (rightInvSeq L n).isHomogeneous_γ.map_mem hz
  barDifferential_comp_barMap := LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      coalgHom_rightInvTaylor_apply_of_mem_filtration L hn, (rightInvSeq L n).intertwines z hn,
      coalgHom_rightInvTaylor_apply_of_mem_filtration L (BB.barDifferential_mem_filtration hn)]

private theorem barMap_homotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyInverse.barMap = coalgHom R (rightInvTaylor L) := (rfl)

/-- The linear part of `L.homotopyInverse` is `L.inv`. -/
@[simp]
theorem linearPart_homotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyInverse.linearPart = L.inv :=
  LinearMap.ext fun b ↦ by
    have hb : ofLetter R B b ∈ filtration R B 1 := ofLetter_mem_filtration R B b
    rw [linearPart_apply, taylor_def, LinearMap.comp_apply, barMap_homotopyInverse,
      coalgHom_rightInvTaylor_apply_of_mem_filtration L hb]
    simp only [rightInvSeq, rightInvBase, coalgHom_ofLetter, letter_ofLetter,
      LinearMap.comp_apply]

private theorem homotopyCompHomotopyInverse_barMap_sub (L : LinearHomotopyInverse f) :
    (f.comp L.homotopyInverse).barMap - (AInfinityHom.id BB).barMap =
      BB.barDifferential ∘ₗ
          gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
            (AInfinityHom.id BB).barMap (rightHomotopyTaylor L) +
        gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
            (AInfinityHom.id BB).barMap (rightHomotopyTaylor L) ∘ₗ BB.barDifferential :=
  LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have hD₁ := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
      (f.comp L.homotopyInverse).isCoalgHom_barMap (AInfinityHom.id BB).isCoalgHom_barMap
      (rightHomotopyTaylor L)
    have hD₂ := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (rightInvSeq L n).γ))
      (isCoalgHom_id (R := R) B) (rightInvSeq L n).η
    have hH_eq : ∀ w ∈ filtration R B n,
        gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
          (AInfinityHom.id BB).barMap (rightHomotopyTaylor L) w =
        (rightInvSeq L n).barH w := fun w hw ↦
      hD₁.apply_eq_of_mem_filtration hD₂
        (fun u hu ↦ by
          have hu' := filtration_monotone R B (Nat.sub_le n 1) hu
          rw [barMap_comp, LinearMap.comp_apply, barMap_homotopyInverse,
            coalgHom_rightInvTaylor_apply_of_mem_filtration L hu', LinearMap.comp_apply])
        (fun _ _ ↦ by rw [barMap_id])
        (fun u hu ↦ by
          simp only [← LinearMap.comp_apply (letter R B),
            letter_comp_gradedCoderivAlong, rightHomotopyTaylor_apply_of_mem_filtration L hu]) hw
    have hg_eq : L.homotopyInverse.barMap z = (rightInvSeq L n).barG z :=
      coalgHom_rightInvTaylor_apply_of_mem_filtration L hn
    have hbn := BB.barDifferential_mem_filtration hn
    have heq := (rightInvSeq L n).homotopy_eq z hn
    rw [← RightInvStep.barG, ← RightInvStep.barH] at heq
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at heq ⊢
    rw [hH_eq z hn, hH_eq _ hbn, barMap_comp, LinearMap.comp_apply, hg_eq, barMap_id,
      LinearMap.id_apply]
    exact sub_eq_zero.1 heq

/-- The right `A∞` homotopy from `f.comp L.homotopyInverse` to `AInfinityHom.id BB`. -/
noncomputable def homotopyCompHomotopyInverse (L : LinearHomotopyInverse f) :
    Homotopy (f.comp L.homotopyInverse) (AInfinityHom.id BB) where
  barHomotopy := gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
    (AInfinityHom.id BB).barMap (rightHomotopyTaylor L)
  isGradedCoderivationAlong_barHomotopy :=
    isGradedCoderivationAlong_gradedCoderivAlong _ 1 (f.comp L.homotopyInverse).isCoalgHom_barMap
      (AInfinityHom.id BB).isCoalgHom_barMap _
  isHomogeneous_barHomotopy := by
    refine isHomogeneous_gradedCoderivAlong
      (taylor_def (f.comp L.homotopyInverse) ▸ (f.comp L.homotopyInverse).isHomogeneous_taylor)
      (AInfinityHom.id BB).isHomogeneous_barMap ?_
    refine LinearMap.isHomogeneous_def.2 fun _ z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    rw [rightHomotopyTaylor_apply_of_mem_filtration L hn]
    exact (rightInvSeq L n).isHomogeneous_η.map_mem hz
  barMap_sub_barMap := L.homotopyCompHomotopyInverse_barMap_sub

private theorem barHomotopy_homotopyCompHomotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyCompHomotopyInverse.barHomotopy =
      gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
        (AInfinityHom.id BB).barMap (rightHomotopyTaylor L) := (rfl)

/-- The linear homotopy of `L.homotopyCompHomotopyInverse` is `L.homotopyRight`. -/
@[simp]
theorem linearHomotopy_homotopyCompHomotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyCompHomotopyInverse.linearHomotopy = L.homotopyRight :=
  LinearMap.ext fun b ↦ by
    have hb : ofLetter R B b ∈ filtration R B 1 := ofLetter_mem_filtration R B b
    rw [Homotopy.linearHomotopy_apply, Homotopy.taylor_def, LinearMap.comp_apply,
      barHomotopy_homotopyCompHomotopyInverse, ← LinearMap.comp_apply (letter R B),
      letter_comp_gradedCoderivAlong, rightHomotopyTaylor_apply_of_mem_filtration L hb]
    simp only [rightInvSeq, rightInvBase, LinearMap.comp_apply, letter_ofLetter]

end LinearHomotopyInverse

end AInfinityHom

end TauCeti
