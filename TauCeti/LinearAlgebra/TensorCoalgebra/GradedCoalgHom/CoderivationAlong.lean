/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom

/-!
# Taylor expansion of coderivations along coalgebra morphisms

For coalgebra morphisms `F F' : Tᶜ(M) ⟶ Tᶜ(N)` of reduced tensor coalgebras and a linear map
`δ : Tᶜ(M) ⟶ N` of Taylor components, there is a unique coderivation `D` along `F` and `F'` with
twist parameter `q` whose letter component `π ∘ D` is `δ`.  On a word `x₁ ⋯ xₙ` of homogeneous
letters it sums, over all cuts of the word into nonempty blocks `B₁ ⋯ B_k` and all choices of one
block `B_i`, the word `f(τ B₁) ⋯ f(τ B_{i-1}) δ(B_i) f'(B_{i+1}) ⋯ f'(B_k)`, where `f = π ∘ F`,
`f' = π ∘ F'`, and `τ` is the letterwise Koszul twist of parameter `q`.

Splitting off the first block gives the recursive description
`D(x₁ ⋯ xₙ) = δ(x₁ ⋯ xₙ) + ∑_{0 < d < n} (δ(x₁ ⋯ x_d) · F'(rest) + f(τ(x₁ ⋯ x_d)) · D(rest))`,
from which the co-Leibniz rule follows by induction on word length just as for `coalgHom`.  When
`F` and `F'` have degree zero and `δ` is homogeneous of degree `r`, the resulting coderivation is
homogeneous of degree `r`.

## Main definitions

* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: the coderivation along `F` and `F'` with
  prescribed Taylor components.
* `TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor`: coderivations along coalgebra
  morphisms `F` and `F'` are in bijection with their Taylor components.

## Main results

* `TauCeti.ReducedTensorWords.gradedCoderivAlong_subword`: the recursive evaluation rule on blocks.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong` and
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong`: `gradedCoderivAlong` is an
  `(F, F')`-coderivation with the given letter component.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration`: two
  coderivations along maps agreeing on shorter words agree on the words of length at most `n` once
  their letter components agree there.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: homogeneity of the Taylor
  expansion of homogeneous Taylor components.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6--3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The length-`n` component of `gradedCoderivAlong`: either collapse the whole word by `δ`, or
split off a nonempty first block of `d` letters and apply either `δ` and `F'` or `π ∘ F ∘ τ` and
the shorter expansion. -/
private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if h : 0 < n then ofLetter R N ∘ₗ δ ∘ₗ of R M ⟨n, h⟩ else 0) +
      ∑ d : Fin n, if h : 0 < d.1 then
        TensorProduct.lift (
          (prepend R N).compl₁₂ (δ ∘ₗ of R M ⟨d.1, h⟩)
            (F' ∘ₗ of R M ⟨n - d.1, Nat.sub_pos_of_lt d.2⟩) +
          (prepend R N).compl₁₂
            (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
              of R M ⟨d.1, h⟩)
            (gradedCoderivAlongComponent G q F F' δ (n - d.1))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The coderivation along `F` and `F'` with twist parameter `q` and Taylor components `δ`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    gradedCoderivAlongComponent G q F F' δ n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' δ (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (δ (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          (prepend R N (δ (subword R x 0 d)) (F' (subword R x d (n - d))) +
            prepend R N
              (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x 0 d))))
              (gradedCoderivAlong G q F F' δ (subword R x d (n - d)))) := by
  rw [gradedCoderivAlong, toModule_of, gradedCoderivAlongComponent, dite_eq_left hn,
    ← of_tprod_eq_subword R hn x]
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · rw [dite_eq_right (by omega), hd, subword_length_zero]
    simp only [map_zero, LinearMap.zero_apply, add_zero]
  · have _ := d.isLt
    rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
      subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega), toModule_of]
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
      TensorProduct.lift.tmul, LinearMap.add_apply, LinearMap.compl₁₂_apply]
    have hfirst : of R M ⟨d.1, hd⟩
        (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x (Fin.castLE d.isLt.le i)) =
        of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun j : Fin d.1 ↦ x ⟨0 + j.1, by omega⟩) :=
      of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [hfirst]

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word: either the
whole block is collapsed by `δ`, or a nonempty first block of `d` letters is split off and handled
either by `δ` and `F'` or by `π ∘ F ∘ τ` and the expansion on the rest. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' δ (subword R x a b) =
      ofLetter R N (δ (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          (prepend R N (δ (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
            prepend R N
              (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x a d))))
              (gradedCoderivAlong G q F F' δ (subword R x (a + d) (b - d)))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j hj ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' δ) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' δ hb, hy 0 b (by omega), Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 h with hb | hab
      · have hb0 : b = 0 := by omega
        rw [hb0, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 h with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega)]
      simp only [map_zero, add_zero]

/-- The letter component of `gradedCoderivAlong G q F F' δ` is `δ`. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' δ = δ := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
    map_sum, letter_ofLetter]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong` produces the single letter given by `δ`. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' δ (ofLetter R M a) = ofLetter R N (δ (ofLetter R M a)) := by
  have h := gradedCoderivAlong_subword G q F F' δ (fun _ : Fin 1 ↦ a) 0 1
  rw [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

/-- For coalgebra morphisms `F` and `F'`, `gradedCoderivAlong G q F F' δ` is a coderivation along
`F` and `F'` with twist parameter `q`. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong {G : InternalGrading R M} (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (δ : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' δ) := by
  let τ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
    ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have hFτ : F ∘ₗ τ = coalgHom R (letter R N ∘ₗ (F ∘ₗ τ)) :=
    (hF.comp (isCoalgHom_map _)).eq_coalgHom
  have hFτ_sub : ∀ {n : ℕ} (x : Fin n → M) (a b : ℕ),
      F (τ (subword R x a b)) =
        ofLetter R N (letter R N (F (τ (subword R x a b)))) +
          ∑ d ∈ Finset.range b,
            prepend R N (letter R N (F (τ (subword R x a d))))
              (F (τ (subword R x (a + d) (b - d)))) := fun x a b ↦ by
    have e := LinearMap.congr_fun hFτ (subword R x a b)
    rw [LinearMap.comp_apply, coalgHom_subword] at e
    rw [← hFτ] at e
    simpa only [LinearMap.comp_apply] using e
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      deconcatenation R N (gradedCoderivAlong G q F F' δ (subword R x a b)) =
        TensorProduct.map (gradedCoderivAlong G q F F' δ) F'
            (deconcatenation R M (subword R x a b)) +
          TensorProduct.map (F ∘ₗ τ) (gradedCoderivAlong G q F F' δ)
            (deconcatenation R M (subword R x a b)) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      have hP₁ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N) (prepend R N (δ (subword R x a d)))
              (deconcatenation R N (F' (subword R x (a + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              prepend R N (δ (subword R x a d)) (F' (subword R x (a + d) c)) ⊗ₜ[R]
                F' (subword R x (a + d + c) (b - d - c)) := by
        intro d _
        rw [hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum]
        simp only [LinearMap.rTensor_tmul]
      have hP₂ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N)
              (prepend R N (letter R N (F (τ (subword R x a d)))))
              (deconcatenation R N
                (gradedCoderivAlong G q F F' δ (subword R x (a + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              (prepend R N (letter R N (F (τ (subword R x a d))))
                  (gradedCoderivAlong G q F F' δ (subword R x (a + d) c)) ⊗ₜ[R]
                  F' (subword R x (a + d + c) (b - d - c)) +
                prepend R N (letter R N (F (τ (subword R x a d))))
                  (F (τ (subword R x (a + d) c))) ⊗ₜ[R]
                  gradedCoderivAlong G q F F' δ (subword R x (a + d + c) (b - d - c))) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
        · rw [ih (b - d) (by omega), map_add, map_deconcatenation_subword,
            map_deconcatenation_subword, map_sum, map_sum, ← Finset.sum_add_distrib]
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]
      rw [gradedCoderivAlong_subword, map_add, deconcatenation_ofLetter, zero_add, map_sum,
        map_deconcatenation_subword, map_deconcatenation_subword]
      simp only [map_add, deconcatenation_prepend]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_congr rfl hP₁, Finset.sum_congr rfl hP₂]
      have hRHS₁ :
          ∑ e ∈ Finset.range b,
              gradedCoderivAlong G q F F' δ (subword R x a e) ⊗ₜ[R]
                F' (subword R x (a + e) (b - e)) =
            (∑ e ∈ Finset.range b,
                ofLetter R N (δ (subword R x a e)) ⊗ₜ[R] F' (subword R x (a + e) (b - e))) +
              ((∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                  prepend R N (δ (subword R x a d)) (F' (subword R x (a + d) (e - d))) ⊗ₜ[R]
                    F' (subword R x (a + e) (b - e))) +
                ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                  prepend R N (letter R N (F (τ (subword R x a d))))
                      (gradedCoderivAlong G q F F' δ (subword R x (a + d) (e - d))) ⊗ₜ[R]
                    F' (subword R x (a + e) (b - e))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [gradedCoderivAlong_subword, TensorProduct.add_tmul, TensorProduct.sum_tmul]
        simp only [TensorProduct.add_tmul, Finset.sum_add_distrib, τ]
      have hRHS₂ :
          ∑ e ∈ Finset.range b,
              (F ∘ₗ τ) (subword R x a e) ⊗ₜ[R]
                gradedCoderivAlong G q F F' δ (subword R x (a + e) (b - e)) =
            (∑ e ∈ Finset.range b,
                ofLetter R N (letter R N (F (τ (subword R x a e)))) ⊗ₜ[R]
                  gradedCoderivAlong G q F F' δ (subword R x (a + e) (b - e))) +
              ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (letter R N (F (τ (subword R x a d))))
                    (F (τ (subword R x (a + d) (e - d)))) ⊗ₜ[R]
                  gradedCoderivAlong G q F F' δ (subword R x (a + e) (b - e)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        conv_lhs => rw [LinearMap.comp_apply, hFτ_sub, TensorProduct.add_tmul,
          TensorProduct.sum_tmul]
      rw [hRHS₁, hRHS₂]
      simp only [Finset.sum_add_distrib]
      rw [← Finset.sum_range_diag_flip, ← Finset.sum_range_diag_flip, ← Finset.sum_range_diag_flip]
      have hflip : ∀ (u : ℕ → N) (P : ReducedTensorWords R M → ReducedTensorWords R N),
          P 0 = 0 → ∀ (Q : ReducedTensorWords R M → ReducedTensorWords R N),
            ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range (e + 1),
                prepend R N (u d) (P (subword R x (a + d) (e - d))) ⊗ₜ[R]
                  Q (subword R x (a + d + (e - d)) (b - d - (e - d))) =
              ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (u d) (P (subword R x (a + d) (e - d))) ⊗ₜ[R]
                  Q (subword R x (a + e) (b - e)) := fun u P hP Q ↦ by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, hP, map_zero,
          TensorProduct.zero_tmul, add_zero]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        have had : a + d + (e - d) = a + e := by omega
        have hbd : b - d - (e - d) = b - e := by omega
        rw [had, hbd]
      rw [hflip (fun d ↦ δ (subword R x a d)) F' (map_zero F') F',
        hflip (fun d ↦ letter R N (F (τ (subword R x a d))))
          (gradedCoderivAlong G q F F' δ) (map_zero _) F',
        hflip (fun d ↦ letter R N (F (τ (subword R x a d))))
          (fun w ↦ F (τ w)) (by simp [τ]) (gradedCoderivAlong G q F F' δ)]
      abel
  rw [isGradedCoderivationAlong_iff]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.rTensor_def,
    ← LinearMap.comp_apply (TensorProduct.map F _), ← TensorProduct.map_comp, LinearMap.comp_id,
    of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- A coderivation along coalgebra morphisms is the Taylor expansion of its own letter
component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {G : InternalGrading R M} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Coderivations along coalgebra morphisms `F` and `F'` are in bijection with their Taylor
components, the linear maps from tensor words to single letters.

Its body is sealed; reason about it through
`TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor_apply` and
`TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor_symm_apply`. -/
noncomputable def gradedCoderivAlongEquivTaylor (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') :
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D} ≃
      (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun δ := ⟨gradedCoderivAlong G q F F' δ,
    isGradedCoderivationAlong_gradedCoderivAlong q hF hF' δ⟩
  left_inv D := Subtype.ext (D.2.eq_gradedCoderivAlong hF hF').symm
  right_inv δ := letter_comp_gradedCoderivAlong G q F F' δ

@[simp]
theorem gradedCoderivAlongEquivTaylor_apply (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (D : {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D}) :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 :=
  (rfl)

@[simp]
theorem gradedCoderivAlongEquivTaylor_symm_apply (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (δ : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm δ).1 = gradedCoderivAlong G q F F' δ :=
  (rfl)

/-! ### Conilpotence filtration and homogeneity -/

/-- Two coderivations `D₁` and `D₂`, along pairs `(F₁, F₁')` and `(F₂, F₂')` that agree on the
words of length less than `n`, agree on the words of length at most `n` as soon as their letter
components agree there. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ k < n, ∀ z ∈ filtration R M k, F₁ z = F₂ z)
    (hF' : ∀ k < n, ∀ z ∈ filtration R M k, F₁' z = F₂' z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
  | succ n ih =>
      have ih' : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun k hk w hw ↦ hF k (by omega) w hw)
          (fun k hk w hw ↦ hF' k (by omega) w hw)
          (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
      clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          have hτu : ReducedTensorWords.map (R := R) (G.koszulTwist q) u.1 ∈ filtration R M n :=
            (isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul]
          rw [ih' _ u.2, ih' _ v.2, hF' n (Nat.lt_succ_self n) _ v.2,
            hF n (Nat.lt_succ_self n) _ hτu]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- When `F'` preserves the conilpotence filtration, `gradedCoderivAlong` sends a block of `b`
letters into the words of length at most `b`. -/
theorem gradedCoderivAlong_subword_mem_filtration (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ k, ∀ z ∈ filtration R M k, F' z ∈ filtration R N k)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' δ (subword R x a b) ∈ filtration R N b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero]
      exact Submodule.zero_mem _
    rw [gradedCoderivAlong_subword]
    refine Submodule.add_mem _ (filtration_monotone R N hb (ofLetter_mem_filtration R N _))
      (Submodule.sum_mem _ fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
      exact Submodule.zero_mem _
    · exact Submodule.add_mem _
        (filtration_monotone R N (by omega) (prepend_mem_filtration R N _
          (hF' (b - d) _ (subword_mem_filtration R M x (a + d) le_rfl))))
        (filtration_monotone R N (by omega)
          (prepend_mem_filtration R N _ (ih (b - d) (by omega) (a + d))))

/-- When `F'` preserves the conilpotence filtration, so does `gradedCoderivAlong`. -/
theorem gradedCoderivAlong_mem_filtration (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ k, ∀ z ∈ filtration R M k, F' z ∈ filtration R N k)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F F' δ z ∈ filtration R N n := by
  have h : filtration R M n ≤ (filtration R N n).comap (gradedCoderivAlong G q F F' δ) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _
          (filtration_monotone R N hk (gradedCoderivAlong_subword_mem_filtration G q hF' δ y 0 k.1))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact h hz

/-- A coderivation along coalgebra morphisms does not increase tensor length. -/
theorem IsGradedCoderivationAlong.mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    D z ∈ filtration R N n := by
  rw [hD.eq_gradedCoderivAlong hF hF']
  exact gradedCoderivAlong_mem_filtration G q (fun _ _ hw ↦ hF'.mem_filtration hw) _ hz

/-- The Taylor expansion `gradedCoderivAlong` of components `δ` of degree `r` along degree-zero
maps `F` and `F'` is homogeneous of degree `r`. -/
theorem isHomogeneous_gradedCoderivAlong {G : InternalGrading R M} {H : InternalGrading R N}
    {q r : ℤ} {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {δ : ReducedTensorWords R M →ₗ[R] N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF'₀ : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hδ : LinearMap.IsHomogeneous δ (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' δ) (gradedPiece G) (gradedPiece H) r := by
  have hτ : LinearMap.IsHomogeneous (ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) (gradedPiece G) 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro D z hz
    rw [add_zero, map_koszulTwist_apply_of_mem G hz q]
    exact Submodule.smul_mem _ _ hz
  have hFτ : LinearMap.IsHomogeneous
      (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) H.piece 0 := by
    simpa only [add_zero] using (isHomogeneous_letter H).comp (hF₀.comp hτ)
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' δ w ∈ gradedPiece H (D + r)) hz ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have key : ∀ b a : ℕ, a + b ≤ n →
        gradedCoderivAlong G q F F' δ (subword R x a b) ∈
          gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := by
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        intro a hab
        rw [gradedCoderivAlong_subword]
        refine add_mem ?_ (Submodule.sum_mem _ fun d hd ↦ ?_)
        · exact ofLetter_mem_gradedPiece H (hδ.map_mem (subword_mem_gradedPiece x g hxg a b hab))
        · rw [Finset.mem_range] at hd
          rcases Nat.eq_zero_or_pos d with rfl | hd0
          · rw [subword_length_zero]
            simp only [map_zero, LinearMap.zero_apply, add_zero]
            exact zero_mem _
          · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
                (∑ j ∈ Finset.range d, g (a + j)) +
                  ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
              rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
              simp only [Nat.add_assoc]
            refine add_mem ?_ ?_
            · have heq : ((∑ j ∈ Finset.range b, g (a + j)) + r) =
                  ((∑ j ∈ Finset.range d, g (a + j)) + r) +
                    ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
                rw [hsum]
                ring
              rw [heq]
              refine prepend_mem_gradedPiece
                (hδ.map_mem (subword_mem_gradedPiece x g hxg a d (by omega))) ?_
              simpa only [add_zero] using
                hF'₀.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d) (by omega))
            · have heq : ((∑ j ∈ Finset.range b, g (a + j)) + r) =
                  (∑ j ∈ Finset.range d, g (a + j)) +
                    ((∑ j ∈ Finset.range (b - d), g (a + d + j)) + r) := by
                rw [hsum]
                ring
              rw [heq]
              refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
              simpa only [LinearMap.comp_apply, add_zero] using
                hFτ.map_mem (subword_mem_gradedPiece x g hxg a d (by omega))
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
      rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact key n 0 (by omega)
  · rw [map_zero]
    exact zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

end TauCeti.ReducedTensorWords
