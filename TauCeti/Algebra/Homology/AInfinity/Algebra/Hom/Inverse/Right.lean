/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Basic
import TauCeti.LinearAlgebra.TensorCoalgebra.RelativeCoderivation
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
import Mathlib.Tactic.Abel

/-!
# Simultaneous arity-by-arity construction of right A-infinity homotopy inverses

Constructs a right `A∞` homotopy inverse `L.homotopyInverse : BB ⟶ AA` and a right `A∞` homotopy
`L.homotopyCompHomotopyInverse : Homotopy (f.comp L.homotopyInverse) (id BB)` from linear
chain-homotopy inverse data `L : LinearHomotopyInverse f` over any commutative ring, by a
simultaneous arity-by-arity obstruction induction along the conilpotence filtration.

## Main definitions

* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyInverse`: the `A∞` morphism `BB ⟶ AA`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyCompHomotopyInverse`: the right homotopy.

## Main results

* `TauCeti.AInfinityHom.LinearHomotopyInverse.linearPart_homotopyInverse`: linear part is `L.inv`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.linearHomotopy_homotopyCompHomotopyInverse`:
  arity-one component is `L.homotopyRight`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Theorem 1.3.1.2.
-/

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
variable {L : LinearHomotopyInverse f} {k : ℕ} (S : RightInvStep L k)

private noncomputable abbrev barG := coalgHom R S.γ
private noncomputable abbrev barH := rightBarH f S.γ S.η
private noncomputable abbrev errH := rightErrH f S.γ S.η
private noncomputable def errG := AA.barDifferential ∘ₗ S.barG - S.barG ∘ₗ BB.barDifferential
private noncomputable def obsE : ReducedTensorWords R B →ₗ[R] A := letter R A ∘ₗ S.errG
private noncomputable def obsR : ReducedTensorWords R B →ₗ[R] B := letter R B ∘ₗ S.errH
private noncomputable def delta := L.homotopyLeft ∘ₗ S.obsE - L.inv ∘ₗ S.obsR
private noncomputable def nu : ReducedTensorWords R B →ₗ[R] B :=
  f.linearPart ∘ₗ L.homotopyLeft ∘ₗ S.delta - L.homotopyRight ∘ₗ (S.obsR + f.linearPart ∘ₗ S.delta)
private theorem isHomogeneous_barH : LinearMap.IsHomogeneous S.barH
    (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) (-1) :=
  isHomogeneous_gradedCoderivAlong
    (add_zero (0 : ℤ) ▸ (isHomogeneous_letter (BB.grading.shift 1)).comp
      (add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom S.isHomogeneous_γ)))
    (LinearMap.isHomogeneous_id _) S.isHomogeneous_η
private theorem isHomogeneous_obsR : LinearMap.IsHomogeneous S.obsR
    (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 :=
  add_zero (0 : ℤ) ▸ (isHomogeneous_letter (BB.grading.shift 1)).comp
    (((add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp
        (isHomogeneous_coalgHom S.isHomogeneous_γ)).sub (LinearMap.isHomogeneous_id _)).sub
      ((neg_add_cancel (1 : ℤ) ▸ BB.isHomogeneous_barDifferential.comp S.isHomogeneous_barH).add
        (add_neg_cancel (1 : ℤ) ▸ S.isHomogeneous_barH.comp BB.isHomogeneous_barDifferential)))
private theorem isHomogeneous_delta : LinearMap.IsHomogeneous S.delta
    (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
  have hg := isHomogeneous_coalgHom S.isHomogeneous_γ
  have he := add_zero (1 : ℤ) ▸ (isHomogeneous_letter (AA.grading.shift 1)).comp
    ((zero_add (1 : ℤ) ▸ AA.isHomogeneous_barDifferential.comp hg).sub
      (add_zero (1 : ℤ) ▸ hg.comp BB.isHomogeneous_barDifferential))
  have hL := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyLeft
  have hi := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_inv
  exact (add_neg_cancel (1 : ℤ) ▸ hL.comp he).sub (add_zero (0 : ℤ) ▸ hi.comp S.isHomogeneous_obsR)
private theorem isHomogeneous_nu : LinearMap.IsHomogeneous S.nu
    (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyLeft
  have hhB := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 L.isHomogeneous_homotopyRight
  exact (add_zero (-1 : ℤ) ▸ hf₁.comp (zero_add (-1 : ℤ) ▸ hhA.comp S.isHomogeneous_delta)).sub
    (zero_add (-1 : ℤ) ▸ hhB.comp
      (S.isHomogeneous_obsR.add (add_zero (0 : ℤ) ▸ hf₁.comp S.isHomogeneous_delta)))
private theorem obsE_eq_zero {w} (hw : w ∈ filtration R B k) : S.obsE w = 0 := by
  rw [obsE, errG, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, S.intertwines w hw, sub_self, map_zero]
private theorem obsR_eq_zero {w} (hw : w ∈ filtration R B k) : S.obsR w = 0 := by
  rw [obsR, LinearMap.comp_apply, S.homotopy_eq w hw, map_zero]
private theorem errG_apply_ofLetter {z} (hz : z ∈ filtration R B (k + 1)) :
    S.errG z = ofLetter R A (S.obsE z) :=
  ((AA.isGradedCoderivation_barDifferential.comp_isCoalgHom (isCoalgHom_coalgHom _)
    (isHomogeneous_coalgHom S.isHomogeneous_γ)).sub
    ((isCoalgHom_coalgHom _).comp_isGradedCoderivation
      BB.isGradedCoderivation_barDifferential)).apply_eq_ofLetter_of_mem_filtration
    (fun _ ↦ S.obsE_eq_zero) hz
private theorem errH_apply_ofLetter {z} (hz : z ∈ filtration R B (k + 1)) :
    S.errH z = ofLetter R B (S.obsR z) := by
  have hFc := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.γ)
  exact (isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1 hFc
    (isCoalgHom_id (R := R) B) S.η).sub_comp_add_comp_of_mem_filtration S.isHomogeneous_barH
    (by decide) BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential
    (by decide) BB.isGradedCoderivation_barDifferential hFc (isCoalgHom_id (R := R) B)
    (add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom S.isHomogeneous_γ))
    (fun w hw ↦ by simp only [LinearMap.comp_apply, f.barDifferential_barMap, S.intertwines w hw])
    (fun _ _ ↦ rfl) S.homotopy_eq hz
private theorem obsE_cocycle {z} (hz : z ∈ filtration R B (k + 1)) :
    AA.differential (S.obsE z) + S.obsE (BB.unaryBarDifferential z) = 0 := by
  have herr : AA.barDifferential (S.errG z) + S.errG (BB.barDifferential z) = 0 := by
    have hAA := LinearMap.congr_fun AA.barDifferential_sq (S.barG z)
    have hBB := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_sub]
      at hAA hBB ⊢; rw [hAA, hBB, map_zero]; abel
  have h := congrArg (letter R A) herr
  have hhi : S.errG (BB.higherBarDifferential z) = 0 :=
    sub_eq_zero.2 (S.intertwines _ (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩))
  rwa [map_add, map_zero, S.errG_apply_ofLetter hz, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, letter_ofLetter, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, hhi, add_zero] at h
private theorem obsR_diff_eq {z} (hz : z ∈ filtration R B (k + 1)) :
    BB.differential (S.obsR z) - S.obsR (BB.unaryBarDifferential z) = f.linearPart (S.obsE z) := by
  have herr : BB.barDifferential (S.errH z) - S.errH (BB.barDifferential z) =
      f.barMap (S.errG z) := by
    have h₁ := LinearMap.congr_fun BB.barDifferential_sq (S.barH z)
    have h₂ := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [rightErrH, errG, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂, map_zero, f.barDifferential_barMap]; abel
  have h := congrArg (letter R B) herr
  rwa [map_sub, S.errH_apply_ofLetter hz, S.errG_apply_ofLetter hz, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    letter_ofLetter, letter_ofLetter, BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
    map_add, S.homotopy_eq _ (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩), add_zero] at h
private theorem differential_delta_sub {z} (hz : z ∈ filtration R B (k + 1)) :
    AA.differential (S.delta z) - S.delta (BB.unaryBarDifferential z) = -S.obsE z := by
  have hr := congrArg L.inv (S.obsR_diff_eq hz)
  have hinv := LinearMap.congr_fun L.differential_comp_inv (S.obsR z)
  have hA := LinearMap.congr_fun L.inv_comp_linearPart_sub_id (S.obsE z)
  simp only [delta, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub] at hinv hA hr ⊢
  rw [← hinv] at hr; rw [← hr, eq_neg_of_add_eq_zero_left (S.obsE_cocycle hz), map_neg] at hA
  rw [eq_sub_of_add_eq hA.symm]; abel
private theorem differential_nu_add {z} (hz : z ∈ filtration R B (k + 1)) :
    BB.differential (S.nu z) + S.nu (BB.unaryBarDifferential z) =
      S.obsR z + f.linearPart (S.delta z) := by
  rw [nu]; set r' := S.obsR + f.linearPart ∘ₗ S.delta
  have hdz : S.obsE z = S.delta (BB.unaryBarDifferential z) - AA.differential (S.delta z) := by
    rw [← neg_sub, S.differential_delta_sub hz, neg_neg]
  have hr' : r' (BB.unaryBarDifferential z) = BB.differential (r' z) := by
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (S.delta z)
    simp only [r', LinearMap.add_apply, LinearMap.comp_apply, map_add] at hf₁ ⊢
    rw [sub_eq_iff_eq_add.1 (S.obsR_diff_eq hz), hdz, map_sub, ← hf₁]; abel
  have hB := LinearMap.congr_fun L.linearPart_comp_inv_sub_id (r' z)
  have hA := congrArg f.linearPart (LinearMap.congr_fun L.inv_comp_linearPart_sub_id (S.delta z))
  have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (L.homotopyLeft (S.delta z))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, map_add] at hB hA hf₁ ⊢
  rw [hr', hf₁, eq_sub_of_add_eq hB.symm, eq_sub_of_add_eq hA.symm, eq_add_of_sub_eq hdz.symm]
  simp only [r', delta, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add, map_sub]; abel
private theorem delta_eq_zero {w} (hw : w ∈ filtration R B k) : S.delta w = 0 := by
  simp only [delta, LinearMap.sub_apply, LinearMap.comp_apply, S.obsE_eq_zero hw,
    S.obsR_eq_zero hw, map_zero, sub_self]
private theorem nu_eq_zero {w} (hw : w ∈ filtration R B k) : S.nu w = 0 := by
  simp only [nu, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, S.obsR_eq_zero hw,
    S.delta_eq_zero hw, map_zero, add_zero, sub_self]
private theorem coalgHom_add_delta_eq {w} (hw : w ∈ filtration R B k) :
    coalgHom R (S.γ + S.delta) w = S.barG w :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun _ hu ↦ by simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      LinearMap.add_apply, S.delta_eq_zero hu, add_zero]) hw
private theorem coalgHom_add_delta_filtration_succ {u} (hu : u ∈ filtration R B (k + 1)) :
    coalgHom R (S.γ + S.delta) u = S.barG u + ofLetter R A (S.delta u) :=
  eq_add_of_sub_eq' <| ((isCoalgHom_coalgHom _).sub_apply_eq_ofLetter_of_mem_filtration
    (isCoalgHom_coalgHom _) (fun _ hw ↦ congrArg (letter R A) (S.coalgHom_add_delta_eq hw))
    hu).trans (by simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      LinearMap.add_apply, add_sub_cancel_left])
private theorem next_intertwines {z} (hz : z ∈ filtration R B (k + 1)) :
    AA.barDifferential (coalgHom R (S.γ + S.delta) z) =
      coalgHom R (S.γ + S.delta) (BB.barDifferential z) := by
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add,
    S.coalgHom_add_delta_filtration_succ (BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    S.coalgHom_add_delta_eq (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩)]
  have hE := S.errG_apply_ofLetter hz
  have hd := congrArg (ofLetter R A) (S.differential_delta_sub hz)
  simp only [errG, LinearMap.sub_apply, LinearMap.comp_apply,
    BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_sub, map_neg] at hE hd
  exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hE hd)))
private theorem next_homotopy_eq {z} (hz : z ∈ filtration R B (k + 1)) :
    rightErrH f (S.γ + S.delta) (S.η + S.nu) z = 0 := by
  have hH'c := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S.γ + S.delta))) (isCoalgHom_id B) (S.η + S.nu)
  have hHc := isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.γ)) (isCoalgHom_id B) S.η
  have hFG {w} (hw : w ∈ filtration R B k) := congrArg f.barMap (S.coalgHom_add_delta_eq hw)
  have hl {w} (hw : w ∈ filtration R B k) :
      letter R B (rightBarH f (S.γ + S.delta) (S.η + S.nu) w) = letter R B (S.barH w) := by
    simp only [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
      LinearMap.add_apply, S.nu_eq_zero hw, add_zero]
  have hH_diff {u} (hu : u ∈ filtration R B (k + 1)) :
      rightBarH f (S.γ + S.delta) (S.η + S.nu) u = S.barH u + ofLetter R B (S.nu u) :=
    eq_add_of_sub_eq' <| (hH'c.sub_apply_eq_ofLetter_of_mem_filtration hHc (fun _ ↦ hFG)
      (fun _ _ ↦ rfl) (fun _ ↦ hl) hu).trans (by simp only [← LinearMap.comp_apply (letter R B),
        letter_comp_gradedCoderivAlong, LinearMap.add_apply, add_sub_cancel_left])
  have hR := S.errH_apply_ofLetter hz; have hν := congrArg (ofLetter R B) (S.differential_nu_add hz)
  simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_add] at hR hν ⊢
  rw [S.coalgHom_add_delta_filtration_succ hz, map_add, f.barMap_ofLetter, hH_diff hz, map_add,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    BB.barDifferential_eq_unary_add_higher]
  rw [BB.barDifferential_eq_unary_add_higher] at hR
  simp only [LinearMap.add_apply, map_add] at hR ⊢
  rw [hH_diff (BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    hH'c.apply_eq_of_mem_filtration hHc (fun _ hu ↦ hFG (filtration_monotone R B (Nat.sub_le k 1)
      hu)) (fun _ _ ↦ rfl) (fun _ ↦ hl) (BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩)]
  exact Eq.trans (by abel) (sub_eq_zero.2 (congrArg₂ (· + ·) hR hν.symm))
end RightInvStep

section RightSeq
variable (L : LinearHomotopyInverse f)

private noncomputable def rightInvBase : RightInvStep L 1 where
  γ := L.inv ∘ₗ letter R B
  η := L.homotopyRight ∘ₗ letter R B
  isHomogeneous_γ := add_zero (0 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2
    L.isHomogeneous_inv).comp (isHomogeneous_letter (BB.grading.shift 1))
  isHomogeneous_η := zero_add (-1 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2
    L.isHomogeneous_homotopyRight).comp (isHomogeneous_letter (BB.grading.shift 1))
  intertwines w hw := sub_eq_zero.1 <| apply_eq_zero_of_mem_filtration_one R B
    (f := AA.barDifferential ∘ₗ coalgHom R (L.inv ∘ₗ letter R B) -
      coalgHom R (L.inv ∘ₗ letter R B) ∘ₗ BB.barDifferential)
    (LinearMap.ext fun b ↦ by
      have hd := LinearMap.congr_fun L.differential_comp_inv b
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
        coalgHom_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
        ← AInfinityAlgebra.differential_apply] at hd ⊢; rw [hd, sub_self]) w hw
  homotopy_eq w hw := apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ by
    have hb := congrArg (ofLetter R B) (LinearMap.congr_fun L.linearPart_comp_inv_sub_id b)
    simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, coalgHom_ofLetter, gradedCoderivAlong_ofLetter,
      letter_ofLetter, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, map_sub, map_add] at hb ⊢; exact sub_eq_zero.2 hb) w hw
private noncomputable def rightInvSeq : (k : ℕ) → RightInvStep L (k + 1)
  | 0 => rightInvBase L
  | k + 1 => let s := rightInvSeq k; ⟨s.γ + s.delta, s.η + s.nu,
      s.isHomogeneous_γ.add s.isHomogeneous_delta, s.isHomogeneous_η.add s.isHomogeneous_nu,
      fun _ ↦ s.next_intertwines, fun _ ↦ s.next_homotopy_eq⟩
private theorem rightInvSeq_γ_stab (k : ℕ) : ∀ w ∈ filtration R B k,
    (rightInvSeq L (k + 1)).γ w = (rightInvSeq L k).γ w := fun _ hw ↦ by
  simp only [rightInvSeq, LinearMap.add_apply,
    (rightInvSeq L k).delta_eq_zero (filtration_monotone R B k.le_succ hw), add_zero]
private theorem rightInvSeq_η_stab (k : ℕ) : ∀ w ∈ filtration R B k,
    (rightInvSeq L (k + 1)).η w = (rightInvSeq L k).η w := fun _ hw ↦ by
  simp only [rightInvSeq, LinearMap.add_apply,
    (rightInvSeq L k).nu_eq_zero (filtration_monotone R B k.le_succ hw), add_zero]
private theorem coalgHom_rightInv_eq {n : ℕ} {z} (hz : z ∈ filtration R B n) :
    coalgHom R (stabilisingLinearMap fun k ↦ (rightInvSeq L k).γ) z =
      coalgHom R (rightInvSeq L n).γ z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun _ hw ↦ by rw [← LinearMap.comp_apply (letter R A), ← LinearMap.comp_apply (letter R A),
      letter_comp_coalgHom, letter_comp_coalgHom,
      stabilisingLinearMap_apply_of_mem_filtration (rightInvSeq_γ_stab L) hw]) hz

public section
namespace LinearHomotopyInverse
/-- The `A∞` homotopy inverse `BB ⟶ AA` associated to linear chain-homotopy inverse data for
`f.linearPart`. -/
noncomputable def homotopyInverse : AInfinityHom BB AA where
  barMap := coalgHom R (stabilisingLinearMap fun k ↦ (rightInvSeq L k).γ)
  isCoalgHom_barMap := isCoalgHom_coalgHom _
  isHomogeneous_barMap := isHomogeneous_coalgHom <| isHomogeneous_stabilisingLinearMap
    (rightInvSeq_γ_stab L) fun n ↦ (rightInvSeq L n).isHomogeneous_γ
  barDifferential_comp_barMap := LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, coalgHom_rightInv_eq L hn,
      (rightInvSeq L n).intertwines z (filtration_monotone R B n.le_succ hn),
      coalgHom_rightInv_eq L (BB.barDifferential_mem_filtration hn)]

private theorem barMap_homotopyInverse : L.homotopyInverse.barMap =
    coalgHom R (stabilisingLinearMap fun k ↦ (rightInvSeq L k).γ) := rfl

/-- The linear part of `L.homotopyInverse` is `L.inv`. -/
@[simp] theorem linearPart_homotopyInverse : L.homotopyInverse.linearPart = L.inv :=
  LinearMap.ext fun b ↦ by
    rw [linearPart_apply, taylor_def, LinearMap.comp_apply, barMap_homotopyInverse,
      coalgHom_rightInv_eq L (ofLetter_mem_filtration R B b), coalgHom_ofLetter, letter_ofLetter]
    simp only [rightInvSeq, LinearMap.add_apply,
      (rightInvBase L).delta_eq_zero (ofLetter_mem_filtration R B b), add_zero]
    simp only [rightInvBase, LinearMap.comp_apply, letter_ofLetter]

/-- The right `A∞` homotopy from `f.comp L.homotopyInverse` to `AInfinityHom.id BB`. -/
noncomputable def homotopyCompHomotopyInverse :
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
      have hH {w} (hw : w ∈ filtration R B n) := gradedCoderivAlong_stabilisingLinearMap_apply
        (G := BB.grading.shift 1) (q := 1) (φ := fun k ↦ (rightInvSeq L k).η)
        (f.comp L.homotopyInverse).isCoalgHom_barMap (AInfinityHom.id BB).isCoalgHom_barMap
        (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (rightInvSeq L n).γ)) (isCoalgHom_id B)
        (rightInvSeq_η_stab L)
        (fun _ hu ↦ by
          rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, barMap_homotopyInverse]
          exact congrArg f.barMap
            (coalgHom_rightInv_eq L (filtration_monotone R B (Nat.sub_le n 1) hu)))
        (fun _ _ ↦ by rw [barMap_id]) hw
      have heq := (rightInvSeq L n).homotopy_eq z (filtration_monotone R B n.le_succ hn)
      simp only [rightErrH, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at heq ⊢
      rw [hH hn, hH (BB.barDifferential_mem_filtration hn), barMap_comp, LinearMap.comp_apply,
        barMap_homotopyInverse, coalgHom_rightInv_eq L hn, barMap_id, LinearMap.id_apply]
      exact sub_eq_zero.1 heq }

private theorem barHomotopy_homotopyCompHomotopyInverse :
    L.homotopyCompHomotopyInverse.barHomotopy =
      gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp L.homotopyInverse).barMap
        (AInfinityHom.id BB).barMap (stabilisingLinearMap fun k ↦ (rightInvSeq L k).η) := rfl

/-- The linear homotopy of `L.homotopyCompHomotopyInverse` is `L.homotopyRight`. -/
@[simp] theorem linearHomotopy_homotopyCompHomotopyInverse :
    L.homotopyCompHomotopyInverse.linearHomotopy = L.homotopyRight :=
  LinearMap.ext fun b ↦ by
    rw [Homotopy.linearHomotopy_apply, Homotopy.taylor_def,
      barHomotopy_homotopyCompHomotopyInverse, letter_comp_gradedCoderivAlong,
      stabilisingLinearMap_apply_of_mem_filtration (rightInvSeq_η_stab L)
        (ofLetter_mem_filtration R B b)]
    simp only [rightInvSeq, LinearMap.add_apply,
      (rightInvBase L).nu_eq_zero (ofLetter_mem_filtration R B b), add_zero]
    simp only [rightInvBase, LinearMap.comp_apply, letter_ofLetter]
end LinearHomotopyInverse
end
end RightSeq
end AInfinityHom
end TauCeti
