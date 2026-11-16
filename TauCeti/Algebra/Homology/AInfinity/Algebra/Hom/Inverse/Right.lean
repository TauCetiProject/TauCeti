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

Lifts `L : LinearHomotopyInverse f` over a commutative ring to `L.homotopyInverse : BB ⟶ AA` and
`L.homotopyCompHomotopyInverse : Homotopy (f.comp L.homotopyInverse) (id BB)`.

## References
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Theorem 1.3.1.2.
* M. Markl, *Transferring A-infinity (strongly homotopy associative) structures*, 2006.
-/

public section
namespace TauCeti
open ReducedTensorWords
universe uR uA uB
namespace AInfinityHom
variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {f : AInfinityHom AA BB}

private noncomputable abbrev rightBarH (f : AInfinityHom AA BB)
    (γ : ReducedTensorWords R B →ₗ[R] A) (η : ReducedTensorWords R B →ₗ[R] B) :=
  gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η
private noncomputable def rightErrH (f : AInfinityHom AA BB)
    (γ : ReducedTensorWords R B →ₗ[R] A) (η : ReducedTensorWords R B →ₗ[R] B) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  (f.barMap ∘ₗ coalgHom R γ - LinearMap.id) -
    (BB.barDifferential ∘ₗ rightBarH f γ η + rightBarH f γ η ∘ₗ BB.barDifferential)

private structure RightInvStep (L : LinearHomotopyInverse f) (k : ℕ) where
  γ : ReducedTensorWords R B →ₗ[R] A
  η : ReducedTensorWords R B →ₗ[R] B
  isHomogeneous_γ :
    LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  isHomogeneous_η :
    LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  intertwines : ∀ w ∈ filtration R B k,
    AA.barDifferential (coalgHom R γ w) = coalgHom R γ (BB.barDifferential w)
  homotopy_eq : ∀ w ∈ filtration R B k, rightErrH f γ η w = 0

namespace RightInvStep
variable {L : LinearHomotopyInverse f} {k : ℕ}

private noncomputable abbrev barG (S : RightInvStep L k) := coalgHom R S.γ
private noncomputable abbrev barH (S : RightInvStep L k) := rightBarH f S.γ S.η
private noncomputable abbrev errH (S : RightInvStep L k) := rightErrH f S.γ S.η
private noncomputable def errG (S : RightInvStep L k) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ S.barG - S.barG ∘ₗ BB.barDifferential
private noncomputable def obsE (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] A :=
  letter R A ∘ₗ S.errG
private noncomputable def obsR (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] B :=
  letter R B ∘ₗ S.errH
private noncomputable def delta (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] A :=
  L.homotopyLeft ∘ₗ S.obsE - L.inv ∘ₗ S.obsR
private noncomputable def nu (S : RightInvStep L k) : ReducedTensorWords R B →ₗ[R] B :=
  f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta - L.homotopyRight ∘ₗ (S.obsR + f.linearPart ∘ₗ S.delta)
private theorem isHomogeneous_barH (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.barH (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
  isHomogeneous_gradedCoderivAlong
    ((isHomogeneous_letter (BB.grading.shift 1)).compOfEq
      (f.isHomogeneous_barMap.compOfEq (isHomogeneous_coalgHom S.isHomogeneous_γ) 0) 0)
    (LinearMap.isHomogeneous_id _) S.isHomogeneous_η
private theorem isHomogeneous_obsR (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.obsR (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 :=
  (isHomogeneous_letter (BB.grading.shift 1)).compOfEq
    (((f.isHomogeneous_barMap.compOfEq (isHomogeneous_coalgHom S.isHomogeneous_γ) 0).sub
      (LinearMap.isHomogeneous_id _)).sub
      ((BB.isHomogeneous_barDifferential.compOfEq S.isHomogeneous_barH 0).add
        (S.isHomogeneous_barH.compOfEq BB.isHomogeneous_barDifferential 0))) 0
private theorem isHomogeneous_delta (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.delta (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  have hg := isHomogeneous_coalgHom S.isHomogeneous_γ
  have he := (isHomogeneous_letter (AA.grading.shift 1)).compOfEq
    ((AA.isHomogeneous_barDifferential.compOfEq hg 1).sub
      (hg.compOfEq BB.isHomogeneous_barDifferential 1)) 1
  have hL := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyLeft
  have hi := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_inv
  exact (hL.compOfEq he 0).sub (hi.compOfEq S.isHomogeneous_obsR 0)
private theorem isHomogeneous_nu (S : RightInvStep L k) :
    LinearMap.IsHomogeneous S.nu (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyLeft
  have hhB := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyRight
  exact (hf₁.compOfEq (hhA.compOfEq S.isHomogeneous_delta (-1)) (-1)).sub
    (hhB.compOfEq (S.isHomogeneous_obsR.add (hf₁.compOfEq S.isHomogeneous_delta 0)) (-1))
private theorem obsE_eq_zero (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.obsE w = 0 := by
  rw [obsE, LinearMap.comp_apply, errG, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, S.intertwines w hw, sub_self, map_zero]
private theorem obsR_eq_zero (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.obsR w = 0 := by
  rw [obsR, LinearMap.comp_apply, S.homotopy_eq w hw, map_zero]
private theorem errG_apply_ofLetter (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) : S.errG z = ofLetter R A (S.obsE z) := by
  have hcod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 S.barG S.barG S.errG :=
    (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom (isCoalgHom_coalgHom _)
      (isHomogeneous_coalgHom S.isHomogeneous_γ)).sub
      ((isCoalgHom_coalgHom _).comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential)
  exact hcod.apply_eq_ofLetter_of_mem_filtration (fun _ ↦ S.obsE_eq_zero) hz
private theorem errH_apply_ofLetter (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) : S.errH z = ofLetter R B (S.obsR z) := by
  have hFc := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.γ)
  have hD := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1 hFc
    (isCoalgHom_id (R := R) B) S.η
  exact hD.sub_comp_add_comp_of_mem_filtration S.isHomogeneous_barH (by decide)
    BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFc (isCoalgHom_id (R := R) B)
    (f.isHomogeneous_barMap.compOfEq (isHomogeneous_coalgHom S.isHomogeneous_γ) 0)
    (fun w hw ↦ by simp only [LinearMap.comp_apply, f.barDifferential_barMap, S.intertwines w hw])
    (fun _ _ ↦ rfl) S.homotopy_eq hz
private theorem obsE_cocycle (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    AA.differential (S.obsE z) + S.obsE (BB.unaryBarDifferential z) = 0 := by
  have hbE : AA.barDifferential (S.errG z) + S.errG (BB.barDifferential z) = 0 := by
    have hAA := LinearMap.congr_fun AA.barDifferential_sq (S.barG z)
    have hBB := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_sub]
      at hAA hBB ⊢
    rw [hAA, hBB, map_zero]; abel
  have h := congrArg (letter R A) hbE
  have hhi : S.errG (BB.higherBarDifferential z) = 0 :=
    sub_eq_zero.2 (S.intertwines _ (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩))
  rw [map_add, map_zero, S.errG_apply_ofLetter hz, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, letter_ofLetter, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, hhi, add_zero] at h
  exact h
private theorem obsR_diff_eq (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    BB.differential (S.obsR z) - S.obsR (BB.unaryBarDifferential z) = f.linearPart (S.obsE z) := by
  have hbR : BB.barDifferential (S.errH z) - S.errH (BB.barDifferential z) =
      f.barMap (S.errG z) := by
    have h₁ := LinearMap.congr_fun BB.barDifferential_sq (S.barH z)
    have h₂ := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [rightErrH, errG, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂, map_zero, f.barDifferential_barMap]; abel
  have h := congrArg (letter R B) hbR
  rw [map_sub, S.errH_apply_ofLetter hz, S.errG_apply_ofLetter hz, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    letter_ofLetter, letter_ofLetter, BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
    map_add, S.homotopy_eq _ (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
  exact h
private theorem differential_delta_sub (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    AA.differential (S.delta z) - S.delta (BB.unaryBarDifferential z) = -S.obsE z := by
  have he := S.obsE_cocycle hz; have hr := congrArg L.inv (S.obsR_diff_eq hz)
  have hinv := LinearMap.congr_fun L.differential_comp_inv (S.obsR z)
  have hA := LinearMap.congr_fun L.inv_comp_linearPart_sub_id (S.obsE z)
  simp only [delta, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub] at hinv hA hr ⊢
  rw [← hinv] at hr; rw [← hr, eq_neg_of_add_eq_zero_left he, map_neg] at hA
  rw [eq_sub_of_add_eq hA.symm]; abel
private theorem differential_nu_add (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    BB.differential (S.nu z) + S.nu (BB.unaryBarDifferential z) =
      S.obsR z + f.linearPart (S.delta z) := by
  rw [nu]; set r' := S.obsR + f.linearPart ∘ₗ S.delta
  have hdz : S.obsE z = S.delta (BB.unaryBarDifferential z) - AA.differential (S.delta z) := by
    rw [← neg_sub, S.differential_delta_sub hz, neg_neg]
  have hr' : r' (BB.unaryBarDifferential z) = BB.differential (r' z) := by
    have hz₁ := S.obsR_diff_eq hz
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (S.delta z)
    simp only [r', LinearMap.add_apply, LinearMap.comp_apply, map_add] at hf₁ ⊢
    rw [sub_eq_iff_eq_add.1 hz₁, hdz, map_sub, ← hf₁]; abel
  have hB := LinearMap.congr_fun L.linearPart_comp_inv_sub_id (r' z)
  have hA := congrArg f.linearPart (LinearMap.congr_fun L.inv_comp_linearPart_sub_id (S.delta z))
  have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (L.homotopyLeft (S.delta z))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, map_add] at hB hA hf₁ ⊢
  rw [hr', hf₁, eq_sub_of_add_eq hB.symm, eq_sub_of_add_eq hA.symm, eq_add_of_sub_eq hdz.symm]
  simp only [r', delta, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add, map_sub]; abel
private theorem delta_eq_zero_of_mem_filtration (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.delta w = 0 := by
  simp only [delta, LinearMap.sub_apply, LinearMap.comp_apply, S.obsE_eq_zero hw,
    S.obsR_eq_zero hw, map_zero, sub_self]
private theorem nu_eq_zero_of_mem_filtration (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : S.nu w = 0 := by
  simp only [nu, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, S.obsR_eq_zero hw,
    S.delta_eq_zero_of_mem_filtration hw, map_zero, add_zero, sub_self]
private theorem coalgHom_add_delta_eq (S : RightInvStep L k) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B k) : coalgHom R (S.γ + S.delta) w = S.barG w :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun _ hu ↦ by simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      LinearMap.add_apply, S.delta_eq_zero_of_mem_filtration hu, add_zero]) hw
private theorem coalgHom_add_delta_filtration_succ (S : RightInvStep L k)
    {u : ReducedTensorWords R B} (hu : u ∈ filtration R B (k + 1)) :
    coalgHom R (S.γ + S.delta) u = S.barG u + ofLetter R A (S.delta u) :=
  eq_add_of_sub_eq' <|
    (isCoalgHom_coalgHom _).sub_apply_eq_ofLetter_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun _ hw ↦ congrArg (letter R A) (S.coalgHom_add_delta_eq hw)) hu
      |>.trans (by simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        LinearMap.add_apply, add_sub_cancel_left])
private theorem next_intertwines (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) :
    AA.barDifferential (coalgHom R (S.γ + S.delta) z) =
      coalgHom R (S.γ + S.delta) (BB.barDifferential z) := by
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add,
    S.coalgHom_add_delta_filtration_succ (BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    S.coalgHom_add_delta_eq (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩)]
  have hE := S.errG_apply_ofLetter hz
  rw [errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add] at hE
  have hd := congrArg (ofLetter R A) (S.differential_delta_sub hz)
  simp only [map_sub, map_neg] at hd
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hE hd)))
private theorem next_homotopy_eq (S : RightInvStep L k) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (k + 1)) : rightErrH f (S.γ + S.delta) (S.η + S.nu) z = 0 := by
  have hH'c := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S.γ + S.delta))) (isCoalgHom_id B) (S.η + S.nu)
  have hHc := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.γ)) (isCoalgHom_id B) S.η
  have hFG_eq : ∀ w ∈ filtration R B k,
      (f.barMap ∘ₗ coalgHom R (S.γ + S.delta)) w = (f.barMap ∘ₗ S.barG) w :=
    fun _ hw ↦ by simp only [LinearMap.comp_apply, S.coalgHom_add_delta_eq hw]
  have hl_eq : ∀ w ∈ filtration R B k,
      letter R B (rightBarH f (S.γ + S.delta) (S.η + S.nu) w) = letter R B (S.barH w) :=
    fun _ hw ↦ by simp only [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
      LinearMap.add_apply, S.nu_eq_zero_of_mem_filtration hw, add_zero]
  have hH_eq : ∀ w ∈ filtration R B k, rightBarH f (S.γ + S.delta) (S.η + S.nu) w = S.barH w :=
    fun _ hw ↦ hH'c.apply_eq_of_mem_filtration hHc
      (fun u hu ↦ hFG_eq u (filtration_monotone R B (Nat.sub_le k 1) hu)) (fun _ _ ↦ rfl) hl_eq hw
  have hH_diff {u} (hu : u ∈ filtration R B (k + 1)) :
      rightBarH f (S.γ + S.delta) (S.η + S.nu) u = S.barH u + ofLetter R B (S.nu u) :=
    eq_add_of_sub_eq' <| (hH'c.sub_apply_eq_ofLetter_of_mem_filtration hHc hFG_eq (fun _ _ ↦ rfl)
      hl_eq hu).trans (by simp only [← LinearMap.comp_apply (letter R B),
        letter_comp_gradedCoderivAlong, LinearMap.add_apply, add_sub_cancel_left])
  have hR := S.errH_apply_ofLetter hz
  have hν := congrArg (ofLetter R B) (S.differential_nu_add hz)
  simp only [map_add] at hν
  simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hR ⊢
  rw [BB.barDifferential_eq_unary_add_higher] at hR ⊢
  simp only [LinearMap.add_apply, map_add] at hR ⊢
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, f.barMap_ofLetter, hH_diff hz, map_add,
    map_add, AInfinityAlgebra.unaryBarDifferential_ofLetter,
    AInfinityAlgebra.higherBarDifferential_ofLetter, add_zero,
    ← AInfinityAlgebra.differential_apply,
    hH_diff (BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    hH_eq _ (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩)]
  exact Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hR hν.symm))
end RightInvStep

private noncomputable def rightInvBase (L : LinearHomotopyInverse f) : RightInvStep L 1 where
  γ := L.inv ∘ₗ letter R B
  η := L.homotopyRight ∘ₗ letter R B
  isHomogeneous_γ := (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_inv).compOfEq
    (isHomogeneous_letter (BB.grading.shift 1)) 0
  isHomogeneous_η :=
    (LinearMap.isHomogeneous_shift_piece_iff.2 L.isHomogeneous_homotopyRight).compOfEq
      (isHomogeneous_letter (BB.grading.shift 1)) (-1)
  intertwines w hw := by
    have h0 : (AA.barDifferential ∘ₗ coalgHom R (L.inv ∘ₗ letter R B) -
        coalgHom R (L.inv ∘ₗ letter R B) ∘ₗ BB.barDifferential) ∘ₗ ofLetter R B = 0 :=
      LinearMap.ext fun b ↦ by
        have hd := LinearMap.congr_fun L.differential_comp_inv b
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
          coalgHom_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
          ← AInfinityAlgebra.differential_apply] at hd ⊢
        rw [hd, sub_self]
    exact sub_eq_zero.1 (apply_eq_zero_of_mem_filtration_one R B h0 w hw)
  homotopy_eq w hw := apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ by
    have hb := congrArg (ofLetter R B) (LinearMap.congr_fun L.linearPart_comp_inv_sub_id b)
    simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, coalgHom_ofLetter, gradedCoderivAlong_ofLetter,
      letter_ofLetter, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, map_sub, map_add] at hb ⊢
    exact sub_eq_zero.2 hb) w hw
private noncomputable def rightInvSeq (L : LinearHomotopyInverse f) : (k : ℕ) → RightInvStep L k
  | 0 => let b := rightInvBase L
      ⟨b.γ, b.η, b.isHomogeneous_γ, b.isHomogeneous_η,
        fun w hw ↦ b.intertwines w (filtration_monotone R B (Nat.zero_le 1) hw),
        fun w hw ↦ b.homotopy_eq w (filtration_monotone R B (Nat.zero_le 1) hw)⟩
  | 1 => rightInvBase L
  | k + 2 => let s := rightInvSeq L (k + 1)
      ⟨s.γ + s.delta, s.η + s.nu, s.isHomogeneous_γ.add s.isHomogeneous_delta,
        s.isHomogeneous_η.add s.isHomogeneous_nu, fun _ ↦ s.next_intertwines,
        fun _ ↦ s.next_homotopy_eq⟩
private theorem rightInvSeq_γ_stab (L : LinearHomotopyInverse f) (k : ℕ) :
    ∀ w ∈ filtration R B k, (rightInvSeq L (k + 1)).γ w = (rightInvSeq L k).γ w
  | _, hw => by cases k with
    | zero => rfl
    | succ k => simp only [rightInvSeq, LinearMap.add_apply,
        (rightInvSeq L (k + 1)).delta_eq_zero_of_mem_filtration hw, add_zero]
private theorem rightInvSeq_η_stab (L : LinearHomotopyInverse f) (k : ℕ) :
    ∀ w ∈ filtration R B k, (rightInvSeq L (k + 1)).η w = (rightInvSeq L k).η w
  | _, hw => by cases k with
    | zero => rfl
    | succ k => simp only [rightInvSeq, LinearMap.add_apply,
        (rightInvSeq L (k + 1)).nu_eq_zero_of_mem_filtration hw, add_zero]
private theorem coalgHom_rightInv_eq (L : LinearHomotopyInverse f) {n : ℕ}
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B n) :
    coalgHom R (stabilisingLinearMap fun k ↦ (rightInvSeq L k).γ) z =
      coalgHom R (rightInvSeq L n).γ z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun _ hw ↦ by rw [← LinearMap.comp_apply (letter R A), ← LinearMap.comp_apply (letter R A),
      letter_comp_coalgHom, letter_comp_coalgHom,
      stabilisingLinearMap_apply_of_mem_filtration (rightInvSeq_γ_stab L) hw]) hz

namespace LinearHomotopyInverse
/-- The `A∞` homotopy inverse `BB ⟶ AA` associated to linear chain-homotopy inverse data for
`f.linearPart`. -/
noncomputable def homotopyInverse (L : LinearHomotopyInverse f) : AInfinityHom BB AA where
  barMap := coalgHom R (stabilisingLinearMap fun k ↦ (rightInvSeq L k).γ)
  isCoalgHom_barMap := isCoalgHom_coalgHom _
  isHomogeneous_barMap := isHomogeneous_coalgHom <|
    isHomogeneous_stabilisingLinearMap (rightInvSeq_γ_stab L)
      fun n ↦ (rightInvSeq L n).isHomogeneous_γ
  barDifferential_comp_barMap := LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, coalgHom_rightInv_eq L hn,
      (rightInvSeq L n).intertwines z hn,
      coalgHom_rightInv_eq L (BB.barDifferential_mem_filtration hn)]

/-- The linear part of `L.homotopyInverse` is `L.inv`. -/
@[simp] theorem linearPart_homotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyInverse.linearPart = L.inv :=
  LinearMap.ext fun b ↦ by
    rw [linearPart_apply, taylor_def, LinearMap.comp_apply]
    change letter R A (coalgHom R _ (ofLetter R B b)) = _
    rw [coalgHom_rightInv_eq L (ofLetter_mem_filtration R B b)]
    simp only [rightInvSeq, rightInvBase, coalgHom_ofLetter, letter_ofLetter, LinearMap.comp_apply]

/-- The right `A∞` homotopy from `f.comp L.homotopyInverse` to `AInfinityHom.id BB`. -/
noncomputable def homotopyCompHomotopyInverse (L : LinearHomotopyInverse f) :
    Homotopy (f.comp L.homotopyInverse) (AInfinityHom.id BB) :=
  let ηT := stabilisingLinearMap fun k ↦ (rightInvSeq L k).η
  { barHomotopy := gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
      (AInfinityHom.id BB).barMap ηT
    isGradedCoderivationAlong_barHomotopy :=
      isGradedCoderivationAlong_gradedCoderivAlong _ 1 (f.comp L.homotopyInverse).isCoalgHom_barMap
        (AInfinityHom.id BB).isCoalgHom_barMap ηT
    isHomogeneous_barHomotopy := isHomogeneous_gradedCoderivAlong
      (taylor_def (f.comp L.homotopyInverse) ▸ (f.comp L.homotopyInverse).isHomogeneous_taylor)
      (AInfinityHom.id BB).isHomogeneous_barMap <|
      isHomogeneous_stabilisingLinearMap (rightInvSeq_η_stab L)
        fun n ↦ (rightInvSeq L n).isHomogeneous_η
    barMap_sub_barMap := LinearMap.ext fun z ↦ by
      obtain ⟨n, hn⟩ := exists_mem_filtration R B z
      have hH_eq {w} (hw : w ∈ filtration R B n) :
          gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
            (AInfinityHom.id BB).barMap ηT w = (rightInvSeq L n).barH w :=
        gradedCoderivAlong_stabilisingLinearMap_apply
          (f.comp L.homotopyInverse).isCoalgHom_barMap (AInfinityHom.id BB).isCoalgHom_barMap
          (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) (isCoalgHom_id B)
          (rightInvSeq_η_stab L)
          (fun _ hu ↦ by
            rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply]
            exact congrArg f.barMap
              (coalgHom_rightInv_eq L (filtration_monotone R B (Nat.sub_le n 1) hu)))
          (fun _ _ ↦ by rw [barMap_id]) hw
      have heq := (rightInvSeq L n).homotopy_eq z hn
      simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at heq ⊢
      rw [hH_eq hn, hH_eq (BB.barDifferential_mem_filtration hn), barMap_comp, LinearMap.comp_apply,
        show L.homotopyInverse.barMap z = (rightInvSeq L n).barG z from coalgHom_rightInv_eq L hn,
        barMap_id, LinearMap.id_apply]
      exact sub_eq_zero.1 heq }

/-- The linear homotopy of `L.homotopyCompHomotopyInverse` is `L.homotopyRight`. -/
@[simp] theorem linearHomotopy_homotopyCompHomotopyInverse (L : LinearHomotopyInverse f) :
    L.homotopyCompHomotopyInverse.linearHomotopy = L.homotopyRight :=
  LinearMap.ext fun b ↦ by
    rw [Homotopy.linearHomotopy_apply, Homotopy.taylor_def]
    change (letter R B ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 _ _ _) (ofLetter R B b) = _
    rw [letter_comp_gradedCoderivAlong,
      stabilisingLinearMap_apply_of_mem_filtration (rightInvSeq_η_stab L)
        (ofLetter_mem_filtration R B b)]
    simp only [rightInvSeq, rightInvBase, LinearMap.comp_apply, letter_ofLetter]
end LinearHomotopyInverse
end AInfinityHom
end TauCeti
