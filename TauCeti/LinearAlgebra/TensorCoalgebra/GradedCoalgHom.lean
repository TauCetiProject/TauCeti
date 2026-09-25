/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Graded coalgebra morphisms of reduced tensor coalgebras

Let `M` and `N` carry internal integer gradings `G` and `H`, and give their reduced tensor
coalgebras `Tᶜ(M)` and `Tᶜ(N)` the total letter degree.  This file combines the ungraded
correspondence between coalgebra morphisms `Tᶜ(M) ⟶ Tᶜ(N)` and their Taylor components
(`TauCeti.ReducedTensorWords.coalgHomEquivTaylor`) with the grading, and with graded
coderivations.

First, the Taylor expansion `coalgHom f` of a degree-zero family of components `f` is itself of
degree zero: each word `f(B₁) ⋯ f(B_k)` produced from a cut of a homogeneous word into blocks has
the total degree of the word.

Second, a degree-zero coalgebra morphism `F` intertwines two `q`-twisted graded coderivations
`b_M` of `Tᶜ(M)` and `b_N` of `Tᶜ(N)` as soon as it does so after projection onto single letters:
`b_N ∘ F = F ∘ b_M` if and only if `π ∘ b_N ∘ F = π ∘ F ∘ b_M`, where `π : Tᶜ(N) ⟶ N` is the
letter projection.  Indeed the difference `D = b_N ∘ F - F ∘ b_M` satisfies the co-Leibniz rule
along `F`,

`Δ ∘ D = (D ⊗ F) ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of `Tᶜ(M)`, because a degree-zero map commutes with the
letterwise twists.  Such a map vanishes once its letter component does, by induction along the
conilpotence filtration.  Applied to bar constructions, this is the statement that an `A∞`
morphism is determined by, and may be constructed from, Taylor components satisfying the
suspended component equation.

## Main results

* `TauCeti.ReducedTensorWords.isHomogeneous_coalgHom`: the Taylor expansion of degree-zero
  components has degree zero.
* `TauCeti.ReducedTensorWords.IsCoalgHom.comp_eq_comp_iff_letter_comp_eq`: a degree-zero coalgebra
  morphism intertwines two graded coderivations exactly when it does so on letter components.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

namespace ReducedTensorWords

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {G : InternalGrading R M} {H : InternalGrading R N}

/-- The Taylor expansion of components of degree zero has degree zero: every word
`f(B₁) ⋯ f(B_k)` it produces from a homogeneous word has the total degree of that word. -/
theorem isHomogeneous_coalgHom {f : ReducedTensorWords R M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous f (gradedPiece G) H.piece 0) :
    LinearMap.IsHomogeneous (coalgHom R f) (gradedPiece G) (gradedPiece H) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero]
  refine gradedPiece_induction (motive := fun w ↦ coalgHom R f w ∈ gradedPiece H D) hz ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    -- Extend the degrees to absolute positions, and induct on the length of a block.
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have key : ∀ b a : ℕ, a + b ≤ n →
        coalgHom R f (subword R x a b) ∈ gradedPiece H (∑ j ∈ Finset.range b, g (a + j)) := by
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        intro a hab
        rw [coalgHom_subword]
        refine add_mem ?_ (Submodule.sum_mem _ fun d hd ↦ ?_)
        · refine ofLetter_mem_gradedPiece H ?_
          simpa only [add_zero] using hf.map_mem (subword_mem_gradedPiece x g hxg a b hab)
        · rw [Finset.mem_range] at hd
          rcases Nat.eq_zero_or_pos d with rfl | hd0
          · rw [subword_length_zero, map_zero, LinearMap.map_zero₂]
            exact zero_mem _
          · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
                (∑ j ∈ Finset.range d, g (a + j)) +
                  ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
              rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
              simp only [Nat.add_assoc]
            rw [hsum]
            refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
            simpa only [add_zero] using
              hf.map_mem (subword_mem_gradedPiece x g hxg a d (by omega))
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

/-- A degree-zero coalgebra morphism intertwines a `q`-twisted graded coderivation of `Tᶜ(M)`
with one of `Tᶜ(N)` as soon as it does so after projection onto single letters. -/
theorem IsCoalgHom.comp_eq_comp_of_letter_comp_eq
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {q : ℤ}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G q bM) (hbN : IsGradedCoderivation H q bN)
    (hl : letter R N ∘ₗ bN ∘ₗ F = letter R N ∘ₗ F ∘ₗ bM) : bN ∘ₗ F = F ∘ₗ bM := by
  -- A degree-zero map commutes with the letterwise Koszul twists.
  have hτ : ∀ z, ReducedTensorWords.map (R := R) (H.koszulTwist q) (F z) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) z) := fun z ↦ by
    have h := LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) z
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using h
  -- The difference `D = b_N ∘ F - F ∘ b_M` vanishes along the conilpotence filtration.
  have key : ∀ n : ℕ, ∀ z ∈ filtration R M n, bN (F z) = F (bM z) := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [filtration_zero] at hz
        simp only [(Submodule.mem_bot R).1 hz, map_zero]
    | succ n ih =>
        intro z hz
        refine eq_of_deconcatenation_eq_of_letter_eq R N ?_
          (by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hl z)
        obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
        rw [hbN.deconcatenation_apply, hF.deconcatenation_apply, hF.deconcatenation_apply,
          hbM.deconcatenation_apply, ← hw]
        clear hw
        induction w using TensorProduct.inductionOn with
        | tmul u v =>
            simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
              LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add]
            rw [ih _ u.2, ih _ v.2, hτ]
        | add u v hu hv =>
            simp only [map_add] at hu hv ⊢
            rw [add_add_add_comm, hu, hv, add_add_add_comm]
  refine LinearMap.ext fun z ↦ ?_
  have hz : z ∈ ⨆ n : ℕ, filtration R M n := by rw [iSup_filtration_eq_top]; trivial
  obtain ⟨n, hn⟩ :=
    (Submodule.mem_iSup_of_directed _ (filtration_monotone R M).directed_le).1 hz
  exact key n z hn

/-- A degree-zero coalgebra morphism intertwines a `q`-twisted graded coderivation of `Tᶜ(M)`
with one of `Tᶜ(N)` if and only if it does so after projection onto single letters. -/
theorem IsCoalgHom.comp_eq_comp_iff_letter_comp_eq
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {q : ℤ}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G q bM) (hbN : IsGradedCoderivation H q bN) :
    bN ∘ₗ F = F ∘ₗ bM ↔ letter R N ∘ₗ bN ∘ₗ F = letter R N ∘ₗ F ∘ₗ bM :=
  ⟨fun h ↦ by rw [h], hF.comp_eq_comp_of_letter_comp_eq hF₀ hbM hbN⟩

end ReducedTensorWords

end TauCeti
