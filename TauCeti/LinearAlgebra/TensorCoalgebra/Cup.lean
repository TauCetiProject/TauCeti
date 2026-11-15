/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom

/-!
# Cup operator of coderivations along coalgebra morphisms

Let `M` and `N` carry internal integer gradings `G` and `H`, and let `F`, `F'`, `F''` be coalgebra
morphisms `Tᶜ(M) ⟶ Tᶜ(N)`.  Given a `q`-twisted `(F, F')`-coderivation `D₁` and a `q`-twisted
`(F', F'')`-coderivation `D₂`, the naive sum `D₁ + D₂` is not a coderivation along `F` and `F''`:
on each cut `u ⊗ v` of a word, `Δ ∘ (D₁ + D₂)` contains the mismatched cross terms
`D₁ u ⊗ F' v` and `F' (τ_q u) ⊗ D₂ v`.

Following Lefèvre-Hasegawa and Prouté, the *cup operator* `U = gradedCoderivCup G q F D₁ D₂` is the
unique linear map `Tᶜ(M) ⟶ Tᶜ(N)` with vanishing letter component satisfying the second-order
co-Leibniz identity

`Δ ∘ U = (U ⊗ F'') ∘ Δ + (D₁ ⊗ D₂) ∘ (τ_q ⊗ 1) ∘ Δ + (F ⊗ U) ∘ Δ`.

When `F` and `F''` intertwine odd square-zero graded coderivations `b_M` and `b_N` and `D₁`, `D₂`
have odd degree `-1` (so `U` has even degree `-2`), the graded commutator `b_N ∘ U - U ∘ b_M`
cancels the mismatched cross terms of `(b_N ∘ D₁ + D₁ ∘ b_M) ⊗ D₂` and
`D₁ ⊗ (b_N ∘ D₂ + D₂ ∘ b_M)` while having vanishing `[b, -]`-commutator itself.  Both its
co-Leibniz rule and its filtration-shift property (on words of length at most `n + 1`, `U` depends
on `D₂` only on words of length at most `n`) are proved here; they supply vertical composition and
inversion of `A∞` homotopies.

## Main definitions

* `TauCeti.ReducedTensorWords.gradedCoderivCup`: the cup operator pairing `D₁` and `D₂` over `F`.

## Main results

* `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivCup`: `gradedCoderivCup` has zero letter
  component.
* `TauCeti.ReducedTensorWords.gradedCoderivCup_apply_eq_of_mem_filtration`: on `filtration (n + 1)`,
  `gradedCoderivCup` depends on `D₂` only on `filtration n`.
* `TauCeti.ReducedTensorWords.deconcatenation_gradedCoderivCup_of_mem_filtration` and
  `TauCeti.ReducedTensorWords.deconcatenation_comp_gradedCoderivCup`: the cup co-Leibniz identity,
  on a filtration step and globally.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivCup`: `gradedCoderivCup` adds degrees.
* `TauCeti.ReducedTensorWords.deconcatenation_comp_sub_comp_of_cup`: deconcatenation of the
  commutator `b_N ∘ U - U ∘ b_M` for an even map `U` satisfying the cup co-Leibniz identity.

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Section 1.3.
* A. Prouté, *A-infinity structures: modèles minimaux de Baues--Lemaire et Kadeishvili et
  homologie des fibrations*, Reprints in Theory and Applications of Categories 21 (2011), Chapter 4.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

namespace ReducedTensorWords

section Cup

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- The length-`n` component of `gradedCoderivCup G q F D₁ D₂`: split off a nonempty first block of
`d` letters, and either collapse its `q`-twist by `letter ∘ D₁` and map the rest by `D₂`, or
collapse it by `letter ∘ F` and apply `gradedCoderivCup` recursively to the rest. -/
private noncomputable def gradedCoderivCupComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    ∑ d : Fin n, if h : 0 < d.1 then
      TensorProduct.lift ((prepend R N).compl₁₂
        ((letter R N ∘ₗ D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ
          of R M ⟨d.1, h⟩)
        (D₂ ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩)) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le +
      TensorProduct.lift ((prepend R N).compl₁₂
        ((letter R N ∘ₗ F) ∘ₗ of R M ⟨d.1, h⟩)
        (gradedCoderivCupComponent G q F D₁ D₂ (n - d.1))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
    else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The cup operator pairing a `q`-twisted `(F, F')`-coderivation `D₁` with a `q`-twisted
`(F', F'')`-coderivation `D₂`: the unique map with vanishing letter component whose deconcatenation
is `(U ⊗ F'' + (D₁ ⊗ D₂) ∘ (τ_q ⊗ 1) + F ⊗ U) ∘ Δ`. -/
noncomputable def gradedCoderivCup (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    gradedCoderivCupComponent G q F D₁ D₂ n.1

private theorem gradedCoderivCup_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {n : ℕ} (hn : 0 < n)
    (x : Fin n → M) :
    gradedCoderivCup G q F D₁ D₂ (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ∑ d ∈ Finset.range n,
        (prepend R N
            (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x 0 d))))
            (D₂ (subword R x d (n - d))) +
          prepend R N (letter R N (F (subword R x 0 d)))
            (gradedCoderivCup G q F D₁ D₂ (subword R x d (n - d)))) := by
  rw [gradedCoderivCup, toModule_of, gradedCoderivCupComponent]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · rw [dite_eq_right (by omega)]
    simp only [hd, subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
  · have _ := d.isLt
    have hcast : of R M ⟨d.1, by omega⟩ (PiTensorProduct.tprod R fun i ↦ x (Fin.castLE d.2.le i)) =
        of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x ⟨0 + i.1, by omega⟩) :=
      of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
      subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega), toModule_of]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      TensorPower.splitAt_tprod, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, hcast]

/-- Recursive evaluation of `gradedCoderivCup` on a block of a tensor word. -/
theorem gradedCoderivCup_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {n : ℕ} (x : Fin n → M)
    (a b : ℕ) :
    gradedCoderivCup G q F D₁ D₂ (subword R x a b) =
      ∑ d ∈ Finset.range b,
        (prepend R N
            (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x a d))))
            (D₂ (subword R x (a + d) (b - d))) +
          prepend R N (letter R N (F (subword R x a d)))
            (gradedCoderivCup G q F D₁ D₂ (subword R x (a + d) (b - d)))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j _ ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivCup G q F D₁ D₂) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivCup_of_tprod G q F D₁ D₂ hb]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 h with hb | hab
      · rw [show b = 0 by omega, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 h with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero, map_zero,
        map_zero, add_zero]

/-- `gradedCoderivCup` has vanishing letter component. -/
@[simp]
theorem letter_comp_gradedCoderivCup (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    letter R N ∘ₗ gradedCoderivCup G q F D₁ D₂ = 0 := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivCup_subword, map_sum]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/-- `gradedCoderivCup` vanishes on single letters. -/
@[simp]
theorem gradedCoderivCup_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (a : M) :
    gradedCoderivCup G q F D₁ D₂ (ofLetter R M a) = 0 := by
  have h := gradedCoderivCup_subword G q F D₁ D₂ (fun _ : Fin 1 ↦ a) 0 1
  simp only [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    LinearMap.zero_apply, add_zero] at h
  exact h

/-- On words of length at most `n + 1`, `gradedCoderivCup G q F D₁ D₂` depends on `D₂` only on
words of length at most `n`. -/
theorem gradedCoderivCup_apply_eq_of_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {D₂ D₂' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {n : ℕ}
    (hD₂ : ∀ z ∈ filtration R M n, D₂ z = D₂' z)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    gradedCoderivCup G q F D₁ D₂ z = gradedCoderivCup G q F D₁ D₂' z := by
  have key : ∀ {l : ℕ} (x : Fin l → M) (b a : ℕ), b ≤ n + 1 →
      gradedCoderivCup G q F D₁ D₂ (subword R x a b) =
        gradedCoderivCup G q F D₁ D₂' (subword R x a b) := by
    intro l x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a hb
      rw [gradedCoderivCup_subword, gradedCoderivCup_subword]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
      · rw [hD₂ _ (subword_mem_filtration R M x (a + d) (by omega)),
          ih (b - d) (by omega) (a + d) (by omega)]
  suffices hsub : filtration R M (n + 1) ≤
      LinearMap.eqLocus (gradedCoderivCup G q F D₁ D₂) (gradedCoderivCup G q F D₁ D₂') from hsub hz
  rw [filtration_le_iff]
  rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
      rw [map_smul, map_smul, map_smul, of_tprod_eq_subword R k.2, key y k.1 0 hk]
  | add u v hu hv =>
      rw [map_add, map_add, map_add, hu, hv]

/-- When `D₂` preserves the conilpotence filtration up to `n`, `gradedCoderivCup G q F D₁ D₂`
preserves it up to `n + 1`. -/
theorem gradedCoderivCup_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    (F D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {n : ℕ}
    (hD₂ : ∀ k ≤ n, ∀ w ∈ filtration R M k, D₂ w ∈ filtration R N k)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    gradedCoderivCup G q F D₁ D₂ z ∈ filtration R N (n + 1) := by
  have key : ∀ {l : ℕ} (x : Fin l → M) (b a : ℕ), b ≤ n + 1 →
      gradedCoderivCup G q F D₁ D₂ (subword R x a b) ∈ filtration R N b := by
    intro l x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a hb
      rw [gradedCoderivCup_subword]
      refine Submodule.sum_mem _ fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
        exact Submodule.zero_mem _
      · exact Submodule.add_mem _
          (filtration_monotone R N (by omega) (prepend_mem_filtration R N _
            (hD₂ (b - d) (by omega) _ (subword_mem_filtration R M x (a + d) le_rfl))))
          (filtration_monotone R N (by omega) (prepend_mem_filtration R N _
            (ih (b - d) (by omega) (a + d) (by omega))))
  have hsub : filtration R M (n + 1) ≤
      (filtration R N (n + 1)).comap (gradedCoderivCup G q F D₁ D₂) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _ (filtration_monotone R N hk (key y k.1 0 hk))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact hsub hz

private theorem sum_range_cup_tmul_reindex {n : ℕ} (x : Fin n → M) (a b : ℕ)
    (g : ℕ → ℕ → ReducedTensorWords R N) (hg : ∀ e, g e e = 0)
    (h : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range (e + 1),
        g e d ⊗ₜ[R] h (subword R x (a + d + (e - d)) (b - d - (e - d))) =
      ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
        g e d ⊗ₜ[R] h (subword R x (a + e) (b - e)) := by
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_range_succ, hg e, TensorProduct.zero_tmul, add_zero]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at hd
  rw [show a + d + (e - d) = a + e by omega, show b - d - (e - d) = b - e by omega]

private theorem isCoalgHom_subword_eq {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) {l : ℕ} (x : Fin l → M) (c d : ℕ) :
    F (subword R x c d) =
      ofLetter R N (letter R N (F (subword R x c d))) +
        ∑ k ∈ Finset.range d, prepend R N (letter R N (F (subword R x c k)))
          (F (subword R x (c + k) (d - k))) := by
  have heq := hF.eq_coalgHom
  have hval := LinearMap.congr_fun heq (subword R x c d) |>.trans (coalgHom_subword _ x c d)
  simpa only [← heq, LinearMap.comp_apply] using hval

private theorem isGradedCoderivationAlong_koszulTwist_subword {q : ℤ}
    {F F' D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁) {l : ℕ} (x : Fin l → M) (c d : ℕ) :
    D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x c d)) =
      ofLetter R N (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
          (subword R x c d)))) +
        ∑ k ∈ Finset.range d,
          (prepend R N (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x c k))))
              (F' (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x (c + k) (d - k)))) +
            prepend R N (letter R N (F (subword R x c k)))
              (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x (c + k) (d - k))))) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have heq := (hD₁.comp_map_koszulTwist).eq_gradedCoderivAlong
    (hF.comp (isCoalgHom_map (G.koszulTwist q))) (hF'.comp (isCoalgHom_map (G.koszulTwist q)))
  have hττ : ∀ w, F (τ (τ w)) = F w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.comp_assoc,
      ← map_comp, InternalGrading.koszulTwist_comp_self, map_id, LinearMap.comp_id]
  have hval := LinearMap.congr_fun heq (subword R x c d) |>.trans
    (gradedCoderivAlong_subword G q _ _ _ x c d)
  dsimp only [τ] at hττ ⊢
  simpa only [← heq, LinearMap.comp_apply, hττ] using hval

private theorem rTensor_prepend_deconcatenation_cup_first (G : InternalGrading R M ℤ) (q : ℤ)
    {F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {m : ℕ}
    (hD₂ : ∀ w ∈ filtration R M m,
      deconcatenation R N (D₂ w) =
        TensorProduct.map D₂ F'' (deconcatenation R M w) +
          TensorProduct.map F' D₂
            (LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M w)))
    {l : ℕ} (x : Fin l → M) {b a d : ℕ} (hb : b ≤ m + 1) (hd : d ∈ Finset.range b) :
    LinearMap.rTensor (ReducedTensorWords R N)
        (prepend R N (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
          (subword R x a d)))))
        (deconcatenation R N (D₂ (subword R x (a + d) (b - d)))) =
      ∑ c ∈ Finset.range (b - d),
        (prepend R N (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
            (subword R x a d))))
            (D₂ (subword R x (a + d) c)) ⊗ₜ[R] F'' (subword R x (a + d + c) (b - d - c)) +
          prepend R N (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
            (subword R x a d))))
            (F' (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x (a + d) c))) ⊗ₜ[R]
            D₂ (subword R x (a + d + c) (b - d - c))) := by
  rw [Finset.mem_range] at hd
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
      TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
  · rw [hD₂ _ (subword_mem_filtration R M x (a + d) (by omega)), map_add,
      ← LinearMap.comp_apply (TensorProduct.map F' D₂),
      LinearMap.rTensor_def (ReducedTensorWords R M)
        (ReducedTensorWords.map (R := R) (G.koszulTwist q)),
      ← TensorProduct.map_comp, LinearMap.comp_id, map_deconcatenation_subword,
      map_deconcatenation_subword, map_sum, map_sum, ← Finset.sum_add_distrib]
    simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]

private theorem deconcatenation_gradedCoderivCup_subword {q : ℤ}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁) {m : ℕ}
    (hD₂ : ∀ w ∈ filtration R M m,
      deconcatenation R N (D₂ w) =
        TensorProduct.map D₂ F'' (deconcatenation R M w) +
          TensorProduct.map F' D₂
            (LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M w)))
    {l : ℕ} (x : Fin l → M) (b a : ℕ) (hb : b ≤ m + 1) :
    deconcatenation R N (gradedCoderivCup G q F D₁ D₂ (subword R x a b)) =
      TensorProduct.map (gradedCoderivCup G q F D₁ D₂) F''
          (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂
          (deconcatenation R M (subword R x a b)) +
        TensorProduct.map F (gradedCoderivCup G q F D₁ D₂)
          (deconcatenation R M (subword R x a b)) := by
  set U := gradedCoderivCup G q F D₁ D₂
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    have hP₂ : ∀ d ∈ Finset.range b,
        LinearMap.rTensor (ReducedTensorWords R N) (prepend R N (letter R N (F (subword R x a d))))
            (deconcatenation R N (U (subword R x (a + d) (b - d)))) =
          ∑ c ∈ Finset.range (b - d),
            (prepend R N (letter R N (F (subword R x a d)))
                (U (subword R x (a + d) c)) ⊗ₜ[R] F'' (subword R x (a + d + c) (b - d - c)) +
              prepend R N (letter R N (F (subword R x a d)))
                (D₁ (τ (subword R x (a + d) c))) ⊗ₜ[R]
                D₂ (subword R x (a + d + c) (b - d - c)) +
              prepend R N (letter R N (F (subword R x a d)))
                (F (subword R x (a + d) c)) ⊗ₜ[R] U (subword R x (a + d + c) (b - d - c))) :=
      fun d hd ↦ by
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
        · rw [ih (b - d) (by omega) (a + d) (by omega), map_add, map_add,
            map_deconcatenation_subword, map_deconcatenation_subword, map_deconcatenation_subword,
            map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]
    rw [gradedCoderivCup_subword, map_sum, map_deconcatenation_subword, map_deconcatenation_subword,
      map_deconcatenation_subword]
    simp only [map_add, deconcatenation_prepend, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun d hd ↦ rTensor_prepend_deconcatenation_cup_first G q hD₂ x hb hd),
      Finset.sum_congr rfl hP₂]
    simp only [Finset.sum_add_distrib, ← Finset.sum_range_diag_flip]
    rw [sum_range_cup_tmul_reindex x a b _ (fun _ ↦ by simp [subword_length_zero]),
      sum_range_cup_tmul_reindex x a b _ (fun _ ↦ by simp [subword_length_zero]),
      sum_range_cup_tmul_reindex x a b _ (fun _ ↦ by simp [subword_length_zero]),
      sum_range_cup_tmul_reindex x a b _ (fun _ ↦ by simp [subword_length_zero]),
      sum_range_cup_tmul_reindex x a b _ (fun _ ↦ by simp [subword_length_zero])]
    conv_rhs => enter [1, 1, 2, e]; dsimp only [U]; rw [gradedCoderivCup_subword G q F D₁ D₂ x a e]
    conv_rhs =>
      enter [1, 2, 2, e]
      rw [LinearMap.comp_apply, isGradedCoderivationAlong_koszulTwist_subword hF hF' hD₁ x a e]
    conv_rhs => enter [2, 2, e]; rw [isCoalgHom_subword_eq hF x a e]
    simp only [U, TensorProduct.add_tmul, TensorProduct.sum_tmul, Finset.sum_add_distrib]
    abel

/-- **Cup co-Leibniz rule on a filtration step.**  If `F`, `F'` are coalgebra morphisms, `D₁` is a
`q`-twisted `(F, F')`-coderivation, and `D₂` satisfies the `q`-twisted `(F', F'')`-coderivation rule
on the words of length at most `m`, then `gradedCoderivCup G q F D₁ D₂` satisfies the cup
co-Leibniz rule on the words of length at most `m + 1`. -/
theorem deconcatenation_gradedCoderivCup_of_mem_filtration {q : ℤ}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁) {m : ℕ}
    (hD₂ : ∀ w ∈ filtration R M m,
      deconcatenation R N (D₂ w) =
        TensorProduct.map D₂ F'' (deconcatenation R M w) +
          TensorProduct.map F' D₂
            (LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M w)))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (m + 1)) :
    deconcatenation R N (gradedCoderivCup G q F D₁ D₂ z) =
      TensorProduct.map (gradedCoderivCup G q F D₁ D₂) F'' (deconcatenation R M z) +
        TensorProduct.map D₁ D₂
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) +
        TensorProduct.map F (gradedCoderivCup G q F D₁ D₂) (deconcatenation R M z) := by
  set L : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N ⊗[R] ReducedTensorWords R N :=
    deconcatenation R N ∘ₗ gradedCoderivCup G q F D₁ D₂
  set Q : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N ⊗[R] ReducedTensorWords R N :=
    TensorProduct.map (gradedCoderivCup G q F D₁ D₂) F'' ∘ₗ deconcatenation R M +
      TensorProduct.map D₁ D₂ ∘ₗ LinearMap.rTensor (ReducedTensorWords R M)
        (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M +
      TensorProduct.map F (gradedCoderivCup G q F D₁ D₂) ∘ₗ deconcatenation R M
  suffices hsub : filtration R M (m + 1) ≤ LinearMap.eqLocus L Q from hsub hz
  rw [filtration_le_iff]
  rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
      rw [map_smul, map_smul, map_smul, of_tprod_eq_subword R k.2]
      refine congrArg (r • ·) ?_
      simp only [L, Q, LinearMap.comp_apply, LinearMap.add_apply]
      rw [deconcatenation_gradedCoderivCup_subword hF hF' hD₁ hD₂ y k.1 0 hk,
        ← LinearMap.comp_apply (TensorProduct.map D₁ D₂), LinearMap.rTensor_def,
        ← TensorProduct.map_comp, LinearMap.comp_id]
  | add u v hu hv =>
      rw [map_add, map_add, map_add, hu, hv]

/-- **Global cup co-Leibniz rule.**  When `D₂` is a `q`-twisted `(F', F'')`-coderivation globally,
`gradedCoderivCup G q F D₁ D₂` satisfies the cup co-Leibniz rule on all words. -/
theorem deconcatenation_comp_gradedCoderivCup {q : ℤ}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁)
    (hD₂ : IsGradedCoderivationAlong G q F' F'' D₂) :
    deconcatenation R N ∘ₗ gradedCoderivCup G q F D₁ D₂ =
      TensorProduct.map (gradedCoderivCup G q F D₁ D₂) F'' ∘ₗ deconcatenation R M +
        TensorProduct.map D₁ D₂ ∘ₗ LinearMap.rTensor (ReducedTensorWords R M)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M +
        TensorProduct.map F (gradedCoderivCup G q F D₁ D₂) ∘ₗ deconcatenation R M := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨m, hm⟩ := exists_mem_filtration R M z
  exact deconcatenation_gradedCoderivCup_of_mem_filtration hF hF' hD₁
    (fun w _ ↦ hD₂.deconcatenation_apply w) (filtration_monotone R M m.le_succ hm)

private theorem isHomogeneous_letter_comp_koszulTwist {q r₁ : ℤ}
    {D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) r₁) :
    LinearMap.IsHomogeneous
      (letter R N ∘ₗ D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) H.piece r₁ := by
  have hτ0 : LinearMap.IsHomogeneous (G.koszulTwist q) G.piece G.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hm ↦ by
      simpa only [add_zero] using G.koszulTwist_mem_piece hm q
  simpa only [zero_add, add_zero] using (isHomogeneous_letter H).comp
    (hD₁.comp (isHomogeneous_map G G hτ0))

private theorem gradedCoderivCup_subword_mem_gradedPiece {q r₁ r₂ : ℤ}
    {F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) r₁)
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) r₂)
    {n : ℕ} (x : Fin n → M) (g : ℕ → ℤ) (hxg : ∀ i : Fin n, x i ∈ G.piece (g i))
    (b a : ℕ) (hab : a + b ≤ n) :
    gradedCoderivCup G q F D₁ D₂ (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + (r₁ + r₂)) := by
  have hd₁ := isHomogeneous_letter_comp_koszulTwist (q := q) hD₁
  have hf : LinearMap.IsHomogeneous (letter R N ∘ₗ F) (gradedPiece G) H.piece 0 := by
    simpa only [add_zero] using (isHomogeneous_letter H).comp hF
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [gradedCoderivCup_subword]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, add_zero]; exact zero_mem _
    · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
          (∑ j ∈ Finset.range d, g (a + j)) + ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
        rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
        simp only [Nat.add_assoc]
      have h₁ : prepend R N
          (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
            (subword R x a d))))
          (D₂ (subword R x (a + d) (b - d))) ∈
          gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + (r₁ + r₂)) := by
        rw [hsum, show (∑ j ∈ Finset.range d, g (a + j)) +
            (∑ j ∈ Finset.range (b - d), g (a + d + j)) + (r₁ + r₂) =
            ((∑ j ∈ Finset.range d, g (a + j)) + r₁) +
              ((∑ j ∈ Finset.range (b - d), g (a + d + j)) + r₂) by ring]
        refine prepend_mem_gradedPiece ?_
          (hD₂.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d)))
        simpa only [LinearMap.comp_apply] using
          hd₁.map_mem (subword_mem_gradedPiece x g hxg a d)
      have h₂ : prepend R N (letter R N (F (subword R x a d)))
          (gradedCoderivCup G q F D₁ D₂ (subword R x (a + d) (b - d))) ∈
          gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + (r₁ + r₂)) := by
        rw [hsum, add_assoc]
        refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
        simpa only [add_zero, LinearMap.comp_apply] using
          hf.map_mem (subword_mem_gradedPiece x g hxg a d)
      exact add_mem h₁ h₂

/-- If `F` has degree zero, `D₁` has degree `r₁`, and `D₂` has degree `r₂`, then
`gradedCoderivCup G q F D₁ D₂` is homogeneous of degree `r₁ + r₂`. -/
theorem isHomogeneous_gradedCoderivCup {q r₁ r₂ : ℤ}
    {F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) r₁)
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) r₂) :
    LinearMap.IsHomogeneous (gradedCoderivCup G q F D₁ D₂)
      (gradedPiece G) (gradedPiece H) (r₁ + r₂) := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivCup G q F D₁ D₂ w ∈ gradedPiece H (D + (r₁ + r₂))) hz ?_
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun c _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  intro n hn 𝒟 x hx hD
  set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
  have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
  have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
    rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
  rw [of_tprod_eq_subword R hn, ← hsum]
  exact gradedCoderivCup_subword_mem_gradedPiece hF hD₁ hD₂ x g hxg n 0 (by omega)

end Cup

/-! ### Commutator of a cup operator with odd coderivations -/

section Commutator

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

private theorem map_koszulTwist_of_even {G' : InternalGrading R M ℤ} {H' : InternalGrading R N ℤ}
    {q r : ℤ} {U : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hU : LinearMap.IsHomogeneous U (gradedPiece G') (gradedPiece H') r)
    (hr : (q * r).negOnePow = 1) (w : ReducedTensorWords R M) :
    ReducedTensorWords.map (R := R) (H'.koszulTwist q) (U w) =
      U (ReducedTensorWords.map (R := R) (G'.koszulTwist q) w) := by
  simpa only [hr, Units.val_one, Int.cast_one, one_smul, LinearMap.comp_apply,
    LinearMap.smul_apply] using LinearMap.congr_fun (hU.map_koszulTwist_comp q) w

private theorem map_koszulTwist_of_odd {G' : InternalGrading R M ℤ} {H' : InternalGrading R N ℤ}
    {q r : ℤ} {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : LinearMap.IsHomogeneous D (gradedPiece G') (gradedPiece H') r)
    (hr : (q * r).negOnePow = -1) (w : ReducedTensorWords R M) :
    ReducedTensorWords.map (R := R) (H'.koszulTwist q) (D w) =
      -D (ReducedTensorWords.map (R := R) (G'.koszulTwist q) w) := by
  simpa only [hr, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
    LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD.map_koszulTwist_comp q) w

/-- **Deconcatenation of the commutator of an even cup map with odd coderivations.**  Suppose `F`
and `F''` intertwine odd `q`-twisted coderivations `b_M` and `b_N` (`F` of degree zero), `D₁` has
odd degree `r₁`, and `U` has even degree `r` and satisfies the cup co-Leibniz rule for
`(F, D₁, D₂, F'')` at both `z` and `b_M z`.  Then `b_N ∘ U - U ∘ b_M` has `q`-twisted `(F, F'')`
coderivation terms at `z`, twisted by `(b_N ∘ D₁ + D₁ ∘ b_M) ⊗ D₂ - D₁ ⊗ (b_N ∘ D₂ + D₂ ∘ b_M)`. -/
theorem deconcatenation_comp_sub_comp_of_cup {q r r₁ s : ℤ}
    {F F'' D₁ D₂ U : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hU : LinearMap.IsHomogeneous U (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = 1)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) r₁)
    (hr₁ : (q * r₁).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF'' : bN ∘ₗ F'' = F'' ∘ₗ bM)
    {z : ReducedTensorWords R M}
    (hUz : deconcatenation R N (U z) =
      TensorProduct.map U F'' (deconcatenation R M z) +
        TensorProduct.map D₁ D₂
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) +
        TensorProduct.map F U (deconcatenation R M z))
    (hUbz : deconcatenation R N (U (bM z)) =
      TensorProduct.map U F'' (deconcatenation R M (bM z)) +
        TensorProduct.map D₁ D₂
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M (bM z))) +
        TensorProduct.map F U (deconcatenation R M (bM z))) :
    deconcatenation R N ((bN ∘ₗ U - U ∘ₗ bM) z) =
      TensorProduct.map (bN ∘ₗ U - U ∘ₗ bM) F'' (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ U - U ∘ₗ bM)
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) +
        (TensorProduct.map (bN ∘ₗ D₁ + D₁ ∘ₗ bM) D₂
            (LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) -
          TensorProduct.map D₁ (bN ∘ₗ D₂ + D₂ ∘ₗ bM) (deconcatenation R M z)) := by
  have hττ : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist q)
      (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) = w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hF₁ : ∀ w, bN (F w) = F (bM w) := fun w ↦ LinearMap.congr_fun hF w
  have hF''₁ : ∀ w, bN (F'' w) = F'' (bM w) := fun w ↦ LinearMap.congr_fun hF'' w
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [map_sub, hbN.deconcatenation_apply, hUz, hUbz, hbM.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [map_add, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        map_koszulTwist_of_even (q := q) hF₀ (by rw [mul_zero]; rfl),
        map_koszulTwist_of_even hU hr, map_koszulTwist_of_odd hD₁ hr₁,
        map_koszulTwist_of_odd hbM₁ hs, hττ, hF₁, hF''₁]
      simp only [map_neg, TensorProduct.neg_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
        TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

end Commutator

end ReducedTensorWords

end TauCeti
