/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom

/-!
# Taylor expansion of graded coderivations along coalgebra morphisms

Constructs `TauCeti.ReducedTensorWords.gradedCoderivAlong`, its Taylor equivalence
`gradedCoderivAlongEquivTaylor`, `stabilisingLinearMap`, and filtration bounds for `A∞` homotopies.

## References
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6--3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.2.
-/

public section
open scoped BigOperators DirectSum TensorProduct
universe uR uM uN
namespace TauCeti.ReducedTensorWords

section TaylorExpansion
variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if hn : 0 < n then ofLetter R N ∘ₗ h ∘ₗ of R M ⟨n, hn⟩ else 0) +
      ∑ d : Fin n, if hd : 0 < d.1 then
        (TensorProduct.lift ((prepend R N).compl₁₂ (h ∘ₗ of R M ⟨d.1, hd⟩)
          (F' ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩)) +
        TensorProduct.lift ((prepend R N).compl₁₂
          ((letter R N ∘ₗ F) ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
            of R M ⟨d.1, hd⟩)
          (gradedCoderivAlongComponent G q F F' h (n - d.1)))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The `(F, F')`-coderivation of twist parameter `q` with prescribed Taylor components `h`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ gradedCoderivAlongComponent G q F F' h n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) = ofLetter R N (h (subword R x a b)) +
      ∑ d ∈ Finset.range b, (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
        prepend R N ((letter R N ∘ₗ F)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
          (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d)))) := by
  have hof {m : ℕ} (hm : 0 < m) (y : Fin m → M) :
      gradedCoderivAlong G q F F' h (of R M ⟨m, hm⟩ (PiTensorProduct.tprod R y)) =
        ofLetter R N (h (subword R y 0 m)) + ∑ d ∈ Finset.range m,
          (prepend R N (h (subword R y 0 d)) (F' (subword R y d (m - d))) +
            prepend R N ((letter R N ∘ₗ F)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R y 0 d)))
              (gradedCoderivAlong G q F F' h (subword R y d (m - d)))) := by
    rw [gradedCoderivAlong, toModule_of, gradedCoderivAlongComponent, dite_eq_left hm,
      ← of_tprod_eq_subword R hm y]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [Finset.sum_range]; refine congrArg (_ + ·) (Finset.sum_congr rfl fun d _ ↦ ?_)
    rcases Nat.eq_zero_or_pos d.1 with hd | hd
    · simp [hd, subword_length_zero]
    · have _ := d.isLt
      have hy₀ : of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun i : Fin d.1 ↦
          y (Fin.castLE d.2.le i)) = subword R y 0 d.1 := by
        rw [subword_eq_of_tprod R y hd (by omega)]
        exact of_tprod_congr R M hd rfl fun i ↦ congrArg y (Fin.ext (by simp))
      rw [dite_eq_left hd, subword_eq_of_tprod R y (a := d.1) (b := m - d.1) (by omega) (by omega),
        toModule_of]
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorPower.splitAt_tprod, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, hy₀]
  by_cases hb : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb₀, hab⟩ := hb
    have hy (c d : ℕ) (hcd : c + d ≤ b) :
        subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d = subword R x (a + c) d :=
      subword_congr R _ x hcd (by omega) fun _ _ ↦ congrArg x (Fin.ext (by simp only; omega))
    rw [congrArg (gradedCoderivAlong G q F F' h) (subword_eq_of_tprod R x hb₀ hab), hof hb₀,
      hy 0 b (by omega), Nat.add_zero]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd; rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := (not_and_or.1 hb).elim
      (fun _ ↦ by rw [show b = 0 by omega, subword_length_zero])
      (fun _ ↦ subword_eq_zero_of_lt_add R x (by omega))
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd; rcases not_and_or.1 hb with _ | _
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero, map_zero,
        map_zero, add_zero]

/-- The letter component of `gradedCoderivAlong G q F F' h` is `h`. -/
@[simp] theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' h = h :=
  linearMap_ext R M fun n x ↦ by
    rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
      map_sum, letter_ofLetter]
    simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong` applies the arity-one component of `h`. -/
@[simp] theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' h (ofLetter R M a) = ofLetter R N (h (ofLetter R M a)) := by
  simpa only [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    LinearMap.zero_apply, add_zero] using
    gradedCoderivAlong_subword G q F F' h (fun _ : Fin 1 ↦ a) 0 1

private theorem sum_range_prepend_tmul_flip {n : ℕ} (x : Fin n → M) (a b : ℕ) (u : ℕ → N)
    (L R' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
      prepend R N (u d) (L (subword R x (a + d) c)) ⊗ₜ[R]
        R' (subword R x (a + d + c) (b - d - c))) =
      ∑ e ∈ Finset.range b,
        (∑ d ∈ Finset.range e, prepend R N (u d) (L (subword R x (a + d) (e - d)))) ⊗ₜ[R]
          R' (subword R x (a + e) (b - e)) := by
  rw [← Finset.sum_range_diag_flip]; refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
    TensorProduct.zero_tmul, add_zero, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at hd he
  rw [show a + d + (e - d) = a + e by omega, show b - d - (e - d) = b - e by omega]

/-- **The Taylor expansion `gradedCoderivAlong` is a coderivation along `F` and `F'`** whenever
`F` and `F'` are coalgebra morphisms. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' h) := by
  set D := gradedCoderivAlong G q F F' h with hD_def
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q) with hτ_def
  have key {n : ℕ} (x : Fin n → M) : ∀ b a : ℕ, deconcatenation R N (D (subword R x a b)) =
      TensorProduct.map D F' (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (F ∘ₗ τ) D (deconcatenation R M (subword R x a b)) := by
    intro b; induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      have hDcut : ∀ d ∈ Finset.range b,
          LinearMap.rTensor _ (prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d))))
              (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
            (∑ c ∈ Finset.range (b - d), prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
              (D (subword R x (a + d) c)) ⊗ₜ[R] F' (subword R x (a + d + c) (b - d - c))) +
            ∑ c ∈ Finset.range (b - d), prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
              ((F ∘ₗ τ) (subword R x (a + d) c)) ⊗ₜ[R] D (subword R x (a + d + c) (b - d - c)) :=
        fun d hd ↦ by
          rcases Nat.eq_zero_or_pos d with rfl | _
          · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
              TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero]
          · rw [ih (b - d) (by rw [Finset.mem_range] at hd; omega) (a + d),
              map_deconcatenation_subword, map_deconcatenation_subword, map_add, map_sum, map_sum]
            simp only [LinearMap.rTensor_tmul]
      have hFτ (c : ℕ) : (F ∘ₗ τ) (subword R x a c) =
          ofLetter R N ((letter R N ∘ₗ F) (τ (subword R x a c))) +
            ∑ d ∈ Finset.range c, prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
              ((F ∘ₗ τ) (subword R x (a + d) (c - d))) := by
        simp only [LinearMap.comp_apply, hτ_def]; nth_rw 1 [hF.eq_coalgHom]
        rw [map_subword, coalgHom_subword, ← map_subword]
        refine congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ ?_)
        rw [← map_subword, ← map_subword, ← hF.eq_coalgHom]; rfl
      have hDexp (c : ℕ) : D (subword R x a c) = ofLetter R N (h (subword R x a c)) +
          ∑ d ∈ Finset.range c, (prepend R N (h (subword R x a d))
            (F' (subword R x (a + d) (c - d))) + prepend R N ((letter R N ∘ₗ F)
              (τ (subword R x a d))) (D (subword R x (a + d) (c - d)))) := by
        rw [hD_def, gradedCoderivAlong_subword, ← hD_def, ← hτ_def]
      rw [hDexp b, map_add, deconcatenation_ofLetter, zero_add, map_sum,
        map_deconcatenation_subword, map_deconcatenation_subword]
      simp only [map_add, deconcatenation_prepend, Finset.sum_add_distrib,
        hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum, LinearMap.rTensor_tmul]
      rw [Finset.sum_congr rfl hDcut, Finset.sum_add_distrib, sum_range_prepend_tmul_flip,
        sum_range_prepend_tmul_flip, sum_range_prepend_tmul_flip]
      conv_rhs =>
        rw [Finset.sum_congr rfl fun c _ ↦ congrArg (· ⊗ₜ[R] _) (hDexp c),
          Finset.sum_congr rfl fun c _ ↦ congrArg (· ⊗ₜ[R] _) (hFτ c)]
      simp only [Finset.sum_add_distrib, TensorProduct.add_tmul]; abel
  rw [isGradedCoderivationAlong_iff, LinearMap.rTensor_def, ← LinearMap.comp_assoc,
    ← TensorProduct.map_comp, LinearMap.comp_id]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- Every `(F, F')`-coderivation along coalgebra morphisms `F` and `F'` is the Taylor expansion of
its own letter component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Coderivations along coalgebra morphisms `F` and `F'` are in bijection with their Taylor
components. -/
noncomputable def gradedCoderivAlongEquivTaylor (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') :
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D} ≃ (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun h :=
    ⟨gradedCoderivAlong G q F F' h, isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h⟩
  left_inv D := Subtype.ext (D.2.eq_gradedCoderivAlong hF hF').symm
  right_inv h := letter_comp_gradedCoderivAlong G q F F' h

@[simp] theorem gradedCoderivAlongEquivTaylor_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (D : {D // IsGradedCoderivationAlong G q F F' D}) :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 := (rfl)
@[simp] theorem gradedCoderivAlongEquivTaylor_symm_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm h).1 = gradedCoderivAlong G q F F' h := (rfl)
@[simp] theorem gradedCoderivAlong_zero (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') : gradedCoderivAlong G q F F' 0 = 0 :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' 0).eq_of_letter_comp_eq
    (isGradedCoderivationAlong_zero G q F F')
    (by rw [letter_comp_gradedCoderivAlong, LinearMap.comp_zero])
theorem gradedCoderivAlong_add (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (h₁ h₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (h₁ + h₂) =
      gradedCoderivAlong G q F F' h₁ + gradedCoderivAlong G q F F' h₂ :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _).eq_of_letter_comp_eq
    ((isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h₁).add
      (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h₂))
    (by simp only [letter_comp_gradedCoderivAlong, LinearMap.comp_add])
theorem gradedCoderivAlong_smul (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (c : R) (h : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (c • h) = c • gradedCoderivAlong G q F F' h :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _).eq_of_letter_comp_eq
    ((isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h).smul c)
    (by simp only [letter_comp_gradedCoderivAlong, LinearMap.comp_smul])

/-- **Homogeneity of `gradedCoderivAlong`.** If `π ∘ F` and `F'` have degree zero and `h` has
degree `r`, then `gradedCoderivAlong G q F F' h` has degree `r` for every twist parameter `q`. -/
theorem isHomogeneous_gradedCoderivAlong {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}
    {q r : ℤ} {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {h : ReducedTensorWords R M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous (letter R N ∘ₗ F) (gradedPiece G) H.piece 0)
    (hF' : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' h) (gradedPiece G) (gradedPiece H) r := by
  refine LinearMap.isHomogeneous_def.2 fun D z hz ↦ gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' h w ∈ gradedPiece H (D + r)) hz ?_
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun _ _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ _ hu)
  intro n hn 𝒟 x hx hD
  set g : ℕ → ℤ := fun k ↦ if hk : k < n then 𝒟 ⟨k, hk⟩ else 0 with hg
  have hxg (i : Fin n) : x i ∈ G.piece (g i) := by simpa [hg] using hx i
  have key : ∀ b a : ℕ, a + b ≤ n → gradedCoderivAlong G q F F' h (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := by
    intro b; induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a hab; rw [gradedCoderivAlong_subword]
      refine add_mem
        (ofLetter_mem_gradedPiece H (hh.map_mem (subword_mem_gradedPiece x g hxg a b)))
        (Submodule.sum_mem _ fun d hd ↦ ?_)
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, zero_mem]
      · rw [Finset.mem_range] at hd
        have hsum : ∑ j ∈ Finset.range b, g (a + j) =
            (∑ j ∈ Finset.range d, g (a + j)) + ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
          rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
          simp only [Nat.add_assoc]
        have hsub₁ := subword_mem_gradedPiece x g hxg a d
        have hτ₁ : ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d) ∈
            gradedPiece G (∑ j ∈ Finset.range d, g (a + j)) := by
          rw [map_koszulTwist_apply_of_mem G hsub₁ q]; exact Submodule.smul_mem _ _ hsub₁
        refine add_mem (by
          rw [hsum, add_right_comm]
          exact prepend_mem_gradedPiece (hh.map_mem hsub₁)
            (by simpa only [add_zero] using
              hF'.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d)))) ?_
        rw [hsum, add_assoc]
        exact prepend_mem_gradedPiece (by simpa only [add_zero] using hf.map_mem hτ₁)
          (ih (b - d) (by omega) (a + d) (by omega))
  have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
    rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
    exact Finset.sum_congr rfl fun _ _ ↦ by simp [hg]
  rw [of_tprod_eq_subword R hn, ← hsum]; exact key n 0 (by omega)

private theorem deconcatenation_congr_of_mem_filtration {G : InternalGrading R M ℤ} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, F₁ w = F₂ w) (hF' : ∀ w ∈ filtration R M n, F₁' w = F₂' w)
    (hD : ∀ w ∈ filtration R M n, D₁ w = D₂ w) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N (D₁ z) = deconcatenation R N (D₂ z) := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul]
      rw [hD _ u.2, hD _ v.2, hF' _ v.2,
        hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2)]
  | add _ _ hu hv =>
      simp only [map_add] at hu hv ⊢; rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- **Filtration determination of relative coderivations.** -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {G : InternalGrading R M ℤ} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ w ∈ filtration R M (n - 1), F₁ w = F₂ w)
    (hF' : ∀ w ∈ filtration R M (n - 1), F₁' w = F₂' w)
    (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero => rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
  | succ n ih =>
      rw [Nat.add_sub_cancel] at hF hF'
      refine eq_of_deconcatenation_eq_of_letter_eq R N
        (deconcatenation_congr_of_mem_filtration h₁ h₂ hF hF'
          (fun _ hu ↦ ih (fun w hw ↦ hF w (filtration_monotone R M (Nat.sub_le n 1) hw))
            (fun w hw ↦ hF' w (filtration_monotone R M (Nat.sub_le n 1) hw))
            (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu) hz) (hl z hz)

/-- Assemble a linear map `Tᶜ(M) ⟶ N` whose length-`k` component is taken from `φ k`. -/
noncomputable def stabilisingLinearMap (φ : ℕ → (ReducedTensorWords R M →ₗ[R] N)) :
    ReducedTensorWords R M →ₗ[R] N :=
  DirectSum.toModule R _ _ fun k ↦ φ k.1 ∘ₗ of R M k

/-- If `φ` stabilises along `filtration`, `stabilisingLinearMap φ` agrees with `φ n` on
`filtration n`. -/
theorem stabilisingLinearMap_apply_of_mem_filtration {φ : ℕ → (ReducedTensorWords R M →ₗ[R] N)}
    (hφ : ∀ k, ∀ w ∈ filtration R M k, φ (k + 1) w = φ k w) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    stabilisingLinearMap φ z = φ n z := by
  have hle : ∀ {j m : ℕ}, j ≤ m → ∀ w ∈ filtration R M j, φ m w = φ j w := fun {j m} hjm ↦ by
    induction m, hjm using Nat.le_induction with
    | base => intro _ _; rfl
    | succ m hjm ih => intro w hw; rw [hφ m w (filtration_monotone R M hjm hw), ih w hw]
  refine (show filtration R M n ≤ LinearMap.eqLocus (stabilisingLinearMap φ) (φ n) from ?_) hz
  rw [filtration_le_iff]; rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus, stabilisingLinearMap, toModule_of, LinearMap.comp_apply,
    hle hk _ (of_mem_filtration R M le_rfl x)]

/-- If each `φ n` is homogeneous of degree `r` and `φ` stabilises, `stabilisingLinearMap φ` is
homogeneous of degree `r`. -/
theorem isHomogeneous_stabilisingLinearMap {G : InternalGrading R M ℤ}
    {H : ℤ → Submodule R N} {r : ℤ} {φ : ℕ → (ReducedTensorWords R M →ₗ[R] N)}
    (hφ : ∀ k, ∀ w ∈ filtration R M k, φ (k + 1) w = φ k w)
    (hhom : ∀ n, LinearMap.IsHomogeneous (φ n) (gradedPiece G) H r) :
    LinearMap.IsHomogeneous (stabilisingLinearMap φ) (gradedPiece G) H r :=
  LinearMap.isHomogeneous_def.2 fun _ z hz ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R M z
    rw [stabilisingLinearMap_apply_of_mem_filtration hφ hn]; exact (hhom n).map_mem hz

/-- On `filtration n`, `gradedCoderivAlong` with `stabilisingLinearMap φ` agrees with its `n`-th
stage whenever `F` and `F'` agree with `Fₙ` and `F'ₙ` on `filtration (n - 1)`. -/
theorem gradedCoderivAlong_stabilisingLinearMap_apply {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' Fₙ F'ₙ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hFₙ : IsCoalgHom R Fₙ) (hF'ₙ : IsCoalgHom R F'ₙ)
    {φ : ℕ → (ReducedTensorWords R M →ₗ[R] N)}
    (hφ : ∀ k, ∀ w ∈ filtration R M k, φ (k + 1) w = φ k w) {n : ℕ}
    (hFeq : ∀ w ∈ filtration R M (n - 1), F w = Fₙ w)
    (hF'eq : ∀ w ∈ filtration R M (n - 1), F' w = F'ₙ w)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F F' (stabilisingLinearMap φ) z =
      gradedCoderivAlong G q Fₙ F'ₙ (φ n) z :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong_gradedCoderivAlong G q hFₙ hF'ₙ _) hFeq hF'eq
    (fun _ hu ↦ by rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      letter_comp_gradedCoderivAlong, letter_comp_gradedCoderivAlong,
      stabilisingLinearMap_apply_of_mem_filtration hφ hu]) hz
end TaylorExpansion

section Group
variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem IsGradedCoderivationAlong.neg {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) : IsGradedCoderivationAlong G q F F' (-D) := by
  rw [← neg_one_smul R D]; exact hD.smul (-1 : R)
theorem IsGradedCoderivationAlong.sub {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') :=
  (sub_eq_add_neg D D').symm ▸ hD.add hD'.neg

/-- **Top-arity primitive difference of relative coderivations.** -/
theorem IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration
    {G : InternalGrading R M ℤ} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, F₁ w = F₂ w) (hF' : ∀ w ∈ filtration R M n, F₁' w = F₂' w)
    (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D₁ z - D₂ z = ofLetter R N (letter R N (D₁ z) - letter R N (D₂ z)) := by
  have hdec := deconcatenation_congr_of_mem_filtration h₁ h₂ hF hF'
    (fun _ hu ↦ h₁.apply_eq_of_mem_filtration h₂
      (fun w hw ↦ hF w (filtration_monotone R M (Nat.sub_le n 1) hw))
      (fun w hw ↦ hF' w (filtration_monotone R M (Nat.sub_le n 1) hw)) hl hu) hz
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (by rw [map_sub, letter_ofLetter])
  rw [map_sub, hdec, sub_self, deconcatenation_ofLetter]

/-- A coderivation along `F` and `F'` whose letter component vanishes on `filtration n` takes
single-letter values on `filtration (n + 1)`. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration
    {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ w ∈ filtration R M n, letter R N (D w) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  simpa only [LinearMap.zero_apply, map_zero, sub_zero] using
    hD.sub_apply_eq_ofLetter_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- If `δ` vanishes on `filtration k` and `F`, `F'` are coalgebra morphisms, then
`gradedCoderivAlong G q F F' δ` takes single-letter values `ofLetter (δ z)` on
`filtration (k + 1)`. -/
theorem gradedCoderivAlong_eq_ofLetter_of_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') {δ : ReducedTensorWords R M →ₗ[R] N} {k : ℕ}
    (hδ : ∀ w ∈ filtration R M k, δ w = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (k + 1)) :
    gradedCoderivAlong G q F F' δ z = ofLetter R N (δ z) := by
  simpa only [← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong] using
    (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' δ).apply_eq_ofLetter_of_mem_filtration
      (fun w hw ↦ by rw [← LinearMap.comp_apply, letter_comp_gradedCoderivAlong, hδ w hw]) hz

/-- **Top-arity primitive homotopy residual.** -/
theorem IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1) (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hFc : IsCoalgHom R F) (hF'c : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    (hR : ∀ w ∈ filtration R M n, ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) w = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z =
      ofLetter R N (letter R N (((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z)) := by
  have hτF (w) : ReducedTensorWords.map (R := R) (H.koszulTwist q) (F w) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) w
  have hτD (w) : ReducedTensorWords.map (R := R) (H.koszulTwist q) (D w) =
      (-1 : R) • D (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := by
    simpa only [hr, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) w
  have hτb (w) : ReducedTensorWords.map (R := R) (G.koszulTwist q) (bM w) =
      (-1 : R) • bM (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := by
    simpa only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp q) w
  have hττ (w) : ReducedTensorWords.map (R := R) (G.koszulTwist q)
      (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) = w := by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hneg (x : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) : (-1 : R) • x = -x :=
    @eq_neg_of_add_eq_zero_left (ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) _ _ _ <| by
      nth_rw 2 [← one_smul R x]; rw [← add_smul, neg_add_cancel, zero_smul]
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  simp only [deconcatenation_ofLetter, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_sub, map_add]
  rw [hFc.deconcatenation_apply, hF'c.deconcatenation_apply, hbN.deconcatenation_apply,
    hD.deconcatenation_apply, hD.deconcatenation_apply, hbM.deconcatenation_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hu : bN (D u.1) = F u.1 - F' u.1 - D (bM u.1) :=
        eq_sub_of_add_eq (sub_eq_zero.1 (hR u.1 u.2)).symm
      have hv : bN (D v.1) = F v.1 - F' v.1 - D (bM v.1) :=
        eq_sub_of_add_eq (sub_eq_zero.1 (hR v.1 v.2)).symm
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hτF, hτD, hτb, hττ, map_smul,
        ← TensorProduct.smul_tmul', hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2),
        hF' _ v.2, hu, hv, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      simp only [hneg]; abel
  | add _ _ ih₁ ih₂ =>
      simp only [map_add] at ih₁ ih₂ ⊢
      refine Eq.trans ?_ ((congrArg₂ (· + ·) ih₁ ih₂).trans (add_zero 0)); abel
end Group

end TauCeti.ReducedTensorWords
