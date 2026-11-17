/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom

/-!
# Taylor expansion of graded coderivations along coalgebra morphisms

Constructs the `q`-twisted coderivation `TauCeti.ReducedTensorWords.gradedCoderivAlong G q F F' h`
along coalgebra morphisms `F, F' : Tᶜ(M) ⟶ Tᶜ(N)` with Taylor map `h : Tᶜ(M) ⟶ N`, establishes the
linear equivalence with Taylor components, and proves the filtration-level uniqueness and top-arity
primitivity lemmas underlying inductive `A∞` homotopy constructions.

## Main definitions

* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: `(F, F')`-coderivation with Taylor map `h`.
* `TauCeti.ReducedTensorWords.gradedCoderivationsAlong`: `R`-submodule of relative coderivations.
* `TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor`: linear equivalence with Taylor maps.

## Main results

* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong`: relative co-Leibniz.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: homogeneity of Taylor expansion.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration`: filtration
  determination by letter components.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration`:
  top-arity primitivity of `(F - F') - (bN ∘ D + D ∘ bM)`.

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

section Explicit
variable (G : InternalGrading R M ℤ) (q : ℤ)
  (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)

private noncomputable def gradedCoderivAlongComponent (h : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if hn : 0 < n then ofLetter R N ∘ₗ h ∘ₗ of R M ⟨n, hn⟩ else 0) +
      ∑ d : Fin n, if hd : 0 < d.1 then
        (TensorProduct.lift ((prepend R N).compl₁₂ (h ∘ₗ of R M ⟨d.1, hd⟩)
          (F' ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩)) +
        TensorProduct.lift ((prepend R N).compl₁₂
          ((letter R N ∘ₗ F) ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
            of R M ⟨d.1, hd⟩)
          (gradedCoderivAlongComponent h (n - d.1)))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The `(F, F')`-coderivation of twist parameter `q` with prescribed Taylor components `h`. -/
noncomputable def gradedCoderivAlong (h : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ gradedCoderivAlongComponent G q F F' h n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word. -/
theorem gradedCoderivAlong_subword (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M)
    (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) = ofLetter R N (h (subword R x a b)) +
      ∑ d ∈ Finset.range b, (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
        prepend R N ((letter R N ∘ₗ F)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
          (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d)))) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb₀
  · simp only [subword_length_zero, map_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  by_cases hab : a + b ≤ n
  · set y : Fin b → M := fun j ↦ x ⟨a + j.1, by omega⟩
    have hy (c d : ℕ) (hcd : c + d ≤ b) : subword R y c d = subword R x (a + c) d :=
      subword_congr R y x hcd (by omega) fun _ _ ↦ congrArg x (Fin.ext (by simp only; omega))
    rw [show subword R x a b = of R M ⟨b, hb₀⟩ (PiTensorProduct.tprod R y) from
      subword_eq_of_tprod R x hb₀ hab]; nth_rw 1 [gradedCoderivAlong]
    rw [toModule_of, gradedCoderivAlongComponent, dite_eq_left hb₀]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [Finset.sum_range]; refine congrArg (_ + ·) (Finset.sum_congr rfl fun d _ ↦ ?_)
    rcases Nat.eq_zero_or_pos d.1 with hd | hd
    · simp only [hd, lt_self_iff_false, ↓reduceDIte, LinearMap.zero_apply, subword_length_zero,
        map_zero, add_zero]
    · have hy₀ : of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun i : Fin d.1 ↦
          y (Fin.castLE d.2.le i)) = subword R x a d.1 :=
        (subword_eq_of_tprod R x hd (by have := d.isLt; omega)).symm
      rw [dite_eq_left hd, ← hy d.1 (b - d.1) (by have := d.isLt; omega),
        subword_eq_of_tprod R y (a := d.1) (b := b - d.1) (by have := d.isLt; omega)
          (by have := d.isLt; omega), gradedCoderivAlong, toModule_of]
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorPower.splitAt_tprod, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, hy₀]
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero, map_zero, map_zero, zero_add]
    exact (Finset.sum_eq_zero fun d hd ↦ by
      rw [Finset.mem_range] at hd
      rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero, map_zero,
        map_zero, add_zero]).symm

/-- The letter component of `gradedCoderivAlong G q F F' h` is `h`. -/
@[simp] theorem letter_comp_gradedCoderivAlong (h : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' h = h :=
  linearMap_ext R M fun n x ↦ by
    rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
      map_sum, letter_ofLetter]
    simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong` applies the arity-one component of `h`. -/
@[simp] theorem gradedCoderivAlong_ofLetter (h : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' h (ofLetter R M a) = ofLetter R N (h (ofLetter R M a)) := by
  simpa only [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    LinearMap.zero_apply, add_zero] using
    gradedCoderivAlong_subword G q F F' h (fun _ : Fin 1 ↦ a) 0 1

/-- The `R`-submodule of `q`-twisted coderivations along `F` and `F'`. -/
def gradedCoderivationsAlong :
    Submodule R (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) where
  carrier := {D | IsGradedCoderivationAlong G q F F' D}
  zero_mem' := isGradedCoderivationAlong_zero G q F F'
  add_mem' := IsGradedCoderivationAlong.add
  smul_mem' r _ hD := hD.smul r

private theorem gradedCoderivAlong_smul_add_smul (c₁ c₂ : R)
    (h₁ h₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (c₁ • h₁ + c₂ • h₂) =
      c₁ • gradedCoderivAlong G q F F' h₁ + c₂ • gradedCoderivAlong G q F F' h₂ := by
  have key {m : ℕ} (x : Fin m → M) : ∀ b a : ℕ,
      gradedCoderivAlong G q F F' (c₁ • h₁ + c₂ • h₂) (subword R x a b) =
        c₁ • gradedCoderivAlong G q F F' h₁ (subword R x a b) +
          c₂ • gradedCoderivAlong G q F F' h₂ (subword R x a b) := fun b ↦
    Nat.strong_induction_on b fun b ih a ↦ by
      rw [gradedCoderivAlong_subword, gradedCoderivAlong_subword, gradedCoderivAlong_subword]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_add,
        Finset.smul_sum]
      rw [add_add_add_comm, ← Finset.sum_add_distrib]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun d hd ↦ ?_)
      rw [add_add_add_comm]; congr 1
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]
      · rw [ih (b - d) (by rw [Finset.mem_range] at hd; omega) (a + d), map_add, map_smul, map_smul]
  exact linearMap_ext R M fun n x ↦ by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, of_tprod_eq_subword R n.2] using
      key x n.1 0

/-- `gradedCoderivAlong` is additive in the Taylor map `h`. -/
@[simp] theorem gradedCoderivAlong_add (h₁ h₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (h₁ + h₂) =
      gradedCoderivAlong G q F F' h₁ + gradedCoderivAlong G q F F' h₂ := by
  simpa only [one_smul] using gradedCoderivAlong_smul_add_smul G q F F' 1 1 h₁ h₂

/-- `gradedCoderivAlong` is `R`-homogeneous in the Taylor map `h`. -/
@[simp] theorem gradedCoderivAlong_smul (c : R) (h : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (c • h) = c • gradedCoderivAlong G q F F' h := by
  simpa only [zero_smul, add_zero] using gradedCoderivAlong_smul_add_smul G q F F' c 0 h h

/-- The Taylor expansion of the zero map is zero. -/
@[simp] theorem gradedCoderivAlong_zero : gradedCoderivAlong G q F F' 0 = 0 := by
  simpa only [zero_smul, add_zero] using gradedCoderivAlong_smul_add_smul G q F F' 0 0 0 0
end Explicit

/-- Membership in `gradedCoderivationsAlong` is being a relative coderivation. -/
@[simp] theorem mem_gradedCoderivationsAlong (G : InternalGrading R M ℤ) {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    D ∈ gradedCoderivationsAlong G q F F' ↔ IsGradedCoderivationAlong G q F F' D := Iff.rfl

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
  exact Finset.sum_congr rfl fun d hd ↦ by
    rw [Finset.mem_range] at hd he
    rw [show a + d + (e - d) = a + e by omega, show b - d - (e - d) = b - e by omega]

section CoalgHom
variable (G : InternalGrading R M ℤ) (q : ℤ)
  {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
  (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
include hF hF'

/-- **The Taylor expansion `gradedCoderivAlong` is a coderivation along `F` and `F'`** whenever
`F` and `F'` are coalgebra morphisms. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (h : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' h) := by
  set D := gradedCoderivAlong G q F F' h
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q) with hτ_def
  have key {n : ℕ} (x : Fin n → M) : ∀ b a : ℕ, deconcatenation R N (D (subword R x a b)) =
      TensorProduct.map D F' (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (F ∘ₗ τ) D (deconcatenation R M (subword R x a b)) := fun b ↦
    Nat.strong_induction_on b fun b ih a ↦ by
      set p := fun d ↦ prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
      have hFτ (c : ℕ) : (F ∘ₗ τ) (subword R x a c) =
          ofLetter R N ((letter R N ∘ₗ F) (τ (subword R x a c))) +
            ∑ d ∈ Finset.range c, p d ((F ∘ₗ τ) (subword R x (a + d) (c - d))) := by
        simp only [LinearMap.comp_apply, hτ_def]; nth_rw 1 [hF.eq_coalgHom]
        rw [map_subword, coalgHom_subword, ← map_subword]
        exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ by
          rw [← map_subword, ← map_subword, ← hF.eq_coalgHom])
      have hDexp (c : ℕ) : D (subword R x a c) = ofLetter R N (h (subword R x a c)) +
          ∑ d ∈ Finset.range c, (prepend R N (h (subword R x a d))
            (F' (subword R x (a + d) (c - d))) + p d (D (subword R x (a + d) (c - d)))) :=
        gradedCoderivAlong_subword G q F F' h x a c
      have hDcut : ∀ d ∈ Finset.range b,
          LinearMap.rTensor _ (p d) (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
            (∑ c ∈ Finset.range (b - d), p d (D (subword R x (a + d) c)) ⊗ₜ[R]
              F' (subword R x (a + d + c) (b - d - c))) +
            ∑ c ∈ Finset.range (b - d), p d ((F ∘ₗ τ) (subword R x (a + d) c)) ⊗ₜ[R]
              D (subword R x (a + d + c) (b - d - c)) := fun d hd ↦ by
        rcases Nat.eq_zero_or_pos d with rfl | _
        · simp only [p, subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero]
        · rw [ih (b - d) (by rw [Finset.mem_range] at hd; omega) (a + d),
            map_deconcatenation_subword, map_deconcatenation_subword, map_add, map_sum, map_sum]
          simp only [LinearMap.rTensor_tmul]
      rw [hDexp b, map_add, deconcatenation_ofLetter, zero_add, map_sum,
        map_deconcatenation_subword, map_deconcatenation_subword]
      simp only [map_add, p, deconcatenation_prepend, Finset.sum_add_distrib,
        hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum, LinearMap.rTensor_tmul]
      rw [Finset.sum_congr rfl hDcut, Finset.sum_add_distrib, sum_range_prepend_tmul_flip,
        sum_range_prepend_tmul_flip, sum_range_prepend_tmul_flip]
      conv_rhs =>
        rw [Finset.sum_congr rfl fun c _ ↦ congrArg (· ⊗ₜ[R] _) (hDexp c),
          Finset.sum_congr rfl fun c _ ↦ congrArg (· ⊗ₜ[R] _) (hFτ c)]
      simp only [Finset.sum_add_distrib, TensorProduct.add_tmul]; abel
  rw [isGradedCoderivationAlong_iff, LinearMap.rTensor_def, ← LinearMap.comp_assoc,
    ← TensorProduct.map_comp, LinearMap.comp_id]
  exact linearMap_ext R M fun n x ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, of_tprod_eq_subword R n.2] using
      key x n.1 0

/-- Coderivations along coalgebra morphisms `F` and `F'` are linearly equivalent to their Taylor
components. -/
noncomputable def gradedCoderivAlongEquivTaylor :
    gradedCoderivationsAlong G q F F' ≃ₗ[R] (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun h :=
    ⟨gradedCoderivAlong G q F F' h, isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h⟩
  left_inv D := Subtype.ext (D.2.eq_of_letter_comp_eq
    (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm).symm
  right_inv h := letter_comp_gradedCoderivAlong G q F F' h
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

/-- `gradedCoderivAlongEquivTaylor` sends a relative coderivation to its letter component. -/
@[simp] theorem gradedCoderivAlongEquivTaylor_apply (D : gradedCoderivationsAlong G q F F') :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 := (rfl)

/-- The inverse of `gradedCoderivAlongEquivTaylor` is `gradedCoderivAlong`. -/
@[simp] theorem gradedCoderivAlongEquivTaylor_symm_apply (h : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm h).1 = gradedCoderivAlong G q F F' h := (rfl)
end CoalgHom

/-- Every `(F, F')`-coderivation along coalgebra morphisms `F` and `F'` is the Taylor expansion of
its own letter component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {G : InternalGrading R M ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

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
  have hxg (i : Fin n) : x i ∈ G.piece (g i) := by simpa only [hg, i.isLt, ↓reduceDIte] using hx i
  have key : ∀ b a : ℕ, a + b ≤ n → gradedCoderivAlong G q F F' h (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := fun b ↦
    Nat.strong_induction_on b fun b ih a hab ↦ by
      rw [gradedCoderivAlong_subword]
      refine add_mem
        (ofLetter_mem_gradedPiece H (hh.map_mem (subword_mem_gradedPiece x g hxg a b)))
        (Submodule.sum_mem _ fun d hd ↦ ?_)
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, zero_mem]
      · rw [Finset.mem_range] at hd
        have hsum : ∑ j ∈ Finset.range b, g (a + j) = (∑ j ∈ Finset.range d, g (a + j)) +
            ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
          rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
          simp only [Nat.add_assoc]
        have hsub₁ := subword_mem_gradedPiece x g hxg a d
        rw [hsum]; refine add_mem
          (add_right_comm _ _ r ▸ prepend_mem_gradedPiece (hh.map_mem hsub₁)
            (by simpa only [add_zero] using
              hF'.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d))))
          (add_assoc _ _ r ▸ prepend_mem_gradedPiece
            (by simpa only [add_zero] using hf.map_mem (map_koszulTwist_apply_of_mem G hsub₁ q ▸
              Submodule.smul_mem _ _ hsub₁))
            (ih (b - d) (by omega) (a + d) (by omega)))
  have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D :=
    (Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n).symm.trans <|
      (Finset.sum_congr rfl fun i _ ↦ by
        simp only [hg, Nat.zero_add, i.isLt, ↓reduceDIte, Fin.eta]).trans hD
  rw [of_tprod_eq_subword R hn, ← hsum]; exact key n 0 (by omega)

section Filtration
variable {G : InternalGrading R M ℤ} {q : ℤ}

private theorem deconcatenation_congr_of_mem_filtration
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
        LinearMap.rTensor_tmul, hD _ u.2, hD _ v.2, hF' _ v.2,
        hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2)]
  | add _ _ hu hv =>
      simp only [map_add] at hu hv ⊢; rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- Two relative coderivations agree on `filtration n` when their underlying maps agree on
`filtration (n - 1)` and their letter components agree on `filtration n`. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration
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
      exact eq_of_deconcatenation_eq_of_letter_eq R N
        (deconcatenation_congr_of_mem_filtration h₁ h₂ hF hF'
          (fun _ hu ↦ ih (fun w hw ↦ hF w (filtration_monotone R M (Nat.sub_le n 1) hw))
            (fun w hw ↦ hF' w (filtration_monotone R M (Nat.sub_le n 1) hw))
            (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu) hz) (hl z hz)

/-- On `filtration n`, `gradedCoderivAlong` with `stabilisingLinearMap φ` agrees with its `n`-th
stage whenever `F` and `F'` agree with `Fₙ` and `F'ₙ` on `filtration (n - 1)`. -/
theorem gradedCoderivAlong_stabilisingLinearMap_apply
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
end Filtration
end TaylorExpansion

section Group
variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N]

section GroupImplicit
variable {G : InternalGrading R M ℤ} {q : ℤ}

/-- The negative of a coderivation along `F` and `F'` is a coderivation along `F` and `F'`. -/
theorem IsGradedCoderivationAlong.neg
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) : IsGradedCoderivationAlong G q F F' (-D) :=
  neg_one_smul R D ▸ hD.smul (-1 : R)

/-- The difference of two coderivations along `F` and `F'` is a coderivation along `F` and `F'`. -/
theorem IsGradedCoderivationAlong.sub
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') :=
  (sub_eq_add_neg D D').symm ▸ hD.add hD'.neg

/-- If two relative coderivations and their underlying maps agree on `filtration n`, then their
difference on `filtration (n + 1)` takes single-letter values. -/
theorem IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration
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
  exact eq_of_deconcatenation_eq_of_letter_eq R N
    (by rw [map_sub, hdec, sub_self, deconcatenation_ofLetter]) (by rw [map_sub, letter_ofLetter])

/-- A coderivation along `F` and `F'` whose letter component vanishes on `filtration n` takes
single-letter values on `filtration (n + 1)`. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ w ∈ filtration R M n, letter R N (D w) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  simpa only [LinearMap.zero_apply, map_zero, sub_zero] using
    hD.sub_apply_eq_ofLetter_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- If `F` and `F'` intertwine `bM` and `bN` on `filtration n` and the homotopy residual
`(F - F') - (bN ∘ D + D ∘ bM)` vanishes on `filtration n`, then the residual takes single-letter
values on `filtration (n + 1)`. -/
theorem IsGradedCoderivationAlong.sub_comp_add_comp_of_mem_filtration
    {H : InternalGrading R N ℤ} {r s : ℤ}
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
  set τM := ReducedTensorWords.map (R := R) (G.koszulTwist q) with hτM_def
  set τN := ReducedTensorWords.map (R := R) (H.koszulTwist q) with hτN_def
  have hτF (w) : τN (F w) = F (τM w) := by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) w
  have hτD (w) : τN (D w) = (-1 : R) • D (τM w) := by
    simpa only [hr, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, LinearMap.comp_apply,
      LinearMap.smul_apply] using LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) w
  have hτb (w) : τM (bM w) = (-1 : R) • bM (τM w) := by
    simpa only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, LinearMap.comp_apply,
      LinearMap.smul_apply] using LinearMap.congr_fun (hbM₁.map_koszulTwist_comp q) w
  have hττ (w) : τM (τM w) = w := by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hR' (u : filtration R M n) : bN (D u.1) = F u.1 - F' u.1 - D (bM u.1) :=
    eq_sub_of_add_eq (sub_eq_zero.1 (hR u.1 u.2)).symm
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  simp only [deconcatenation_ofLetter, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_sub, map_add]
  rw [hFc.deconcatenation_apply, hF'c.deconcatenation_apply, hbN.deconcatenation_apply,
    hD.deconcatenation_apply, hD.deconcatenation_apply, hbM.deconcatenation_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, ← hτM_def, ← hτN_def, hτF, hτD, hτb, hττ,
        map_smul, ← TensorProduct.smul_tmul',
        hF (τM u.1) ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2), hF' _ v.2, hR' u,
        hR' v, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      simp only [neg_one_smul R (M := ReducedTensorWords R N ⊗[R] ReducedTensorWords R N)]; abel
  | add _ _ ih₁ ih₂ =>
      simp only [map_add] at ih₁ ih₂ ⊢
      exact Eq.trans (by abel) ((congrArg₂ (· + ·) ih₁ ih₂).trans (add_zero 0))
end GroupImplicit

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
end Group

end TauCeti.ReducedTensorWords
