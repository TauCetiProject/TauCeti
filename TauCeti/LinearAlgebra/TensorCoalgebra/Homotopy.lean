/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom.CoderivationAlong

/-!
# Transitivity and symmetry of homotopies of differential graded coalgebra morphisms

Let `M` and `N` carry internal integer gradings `G` and `H`, let `b_M` and `b_N` be degree-one
square-zero graded coderivations of `Tᶜ(M)` and `Tᶜ(N)` with twist parameter `1`, and let
`F, F', F'' : Tᶜ(M) ⟶ Tᶜ(N)` be degree-zero coalgebra morphisms intertwining `b_M` and `b_N`.
A homotopy from `F` to `F'` is a degree-`(-1)` coderivation `D₁` along `F` and `F'` with twist
parameter `1` satisfying `F - F' = b_N ∘ D₁ + D₁ ∘ b_M`.

Even when `D₁` is an `(F, F')`-coderivation and `D₂` is an `(F', F'')`-coderivation, the naive sum
`D₁ + D₂` is not an `(F, F'')`-coderivation, nor is `-D₁` an `(F', F)`-coderivation: the mismatch
in the co-Leibniz rule is `(F - F') ∘ τ ⊗ D₂ - D₁ ⊗ (F' - F'')` (with `F'' = F` and `D₂` the target
reverse homotopy in the symmetry case).  Following Lefèvre-Hasegawa and Markl, both mismatches are
corrected by the graded commutator `b_N ∘ S - S ∘ b_M` of a degree-`(-2)` map
`S : Tᶜ(M) ⟶ Tᶜ(N)` solving the `(F, F''; D₁, D₂)`-biderivation equation

`Δ ∘ S = (S ⊗ F'' + (D₁ ∘ τ) ⊗ D₂ + F ⊗ S) ∘ Δ`

with vanishing letter component `π ∘ S = 0`, where `τ = map (G.koszulTwist 1)`.  Because every cut
strictly decreases word length and `b_M` preserves the conilpotence filtration, the fixed-point
equations defining `S` for both transitivity and symmetry are contractive along `filtration R M`
and have unique solutions over any commutative ring `R`.

This file also provides `TauCeti.ReducedTensorWords.filtrationLimit`, assembling any sequence of
linear maps out of `Tᶜ(M)` that stabilises on `filtration R M n` into a single linear map.

## Main definitions

* `TauCeti.ReducedTensorWords.filtrationLimit`: the limit of a sequence of linear maps out of
  `Tᶜ(M)` that stabilises along the conilpotence filtration.
* `TauCeti.ReducedTensorWords.homotopyTrans`: composition of an `(F, F')`-coderivation homotopy `D₁`
  with an `(F', F'')`-coderivation homotopy `D₂` into an `(F, F'')`-coderivation homotopy.
* `TauCeti.ReducedTensorWords.homotopySymm`: reversal of an `(F, F')`-coderivation homotopy `D` into
  an `(F', F)`-coderivation homotopy.

## Main results

* `TauCeti.ReducedTensorWords.filtrationLimit_apply_of_mem_filtration`,
  `TauCeti.ReducedTensorWords.isHomogeneous_filtrationLimit`: evaluation and homogeneity of a
  filtration limit.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_homotopyTrans`,
  `TauCeti.ReducedTensorWords.isHomogeneous_homotopyTrans`,
  `TauCeti.ReducedTensorWords.homotopyTrans_eq`: `homotopyTrans` is a degree-`(-1)` coderivation
  along `F` and `F''` satisfying `F - F'' = b_N ∘ D + D ∘ b_M`, with unary part `D₁ + D₂`.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_homotopySymm`,
  `TauCeti.ReducedTensorWords.isHomogeneous_homotopySymm`,
  `TauCeti.ReducedTensorWords.homotopySymm_eq`: `homotopySymm` is a degree-`(-1)` coderivation
  along `F'` and `F` satisfying `F' - F = b_N ∘ D' + D' ∘ b_M`, with unary part `-D`.

## References

* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapter 1, Section 1.2–1.3.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* M. Markl, *Transferring `A∞` (strongly homotopy associative) structures*, Rend. Circ. Mat.
  Palermo (2) Suppl. 79 (2006), 139–151.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti.ReducedTensorWords

/-! ### Limits along the conilpotence filtration -/

section FiltrationLimit

variable {R : Type uR} {M : Type uM} {P : Type uP} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid P] [Module R P]

/-- The limit of a sequence of linear maps `s n : Tᶜ(M) ⟶ P`, taking `s k` on words of length `k`.
When `s (n + 1)` and `s n` agree on `filtration R M n` for every `n`, this limit agrees with `s n`
on `filtration R M n`. -/
noncomputable def filtrationLimit (s : ℕ → (ReducedTensorWords R M →ₗ[R] P)) :
    ReducedTensorWords R M →ₗ[R] P :=
  DirectSum.toModule R {k : ℕ // 0 < k} P fun k ↦ s k.1 ∘ₗ of R M k

/-- In a sequence stabilising on `filtration R M`, `s n` agrees with `s k` on `filtration R M k`
whenever `k ≤ n`. -/
private theorem apply_eq_of_stabilising_of_le {s : ℕ → (ReducedTensorWords R M →ₗ[R] P)}
    (hs : ∀ n, ∀ z ∈ filtration R M n, s (n + 1) z = s n z) {k n : ℕ} (hkn : k ≤ n)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) : s n z = s k z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [hs n z (filtration_monotone R M hkn hz), ih]

/-- On the words of length at most `n`, the filtration limit of a stabilising sequence agrees with
`s n`. -/
theorem filtrationLimit_apply_of_mem_filtration {s : ℕ → (ReducedTensorWords R M →ₗ[R] P)}
    (hs : ∀ n, ∀ z ∈ filtration R M n, s (n + 1) z = s n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    filtrationLimit s z = s n z := by
  have h : filtration R M n ≤ LinearMap.eqLocus (filtrationLimit s) (s n) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, filtrationLimit, toModule_of, LinearMap.comp_apply,
      apply_eq_of_stabilising_of_le hs hk (of_mem_filtration R M le_rfl x)]
  exact h hz

/-- A linear map agreeing with `s n` on `filtration R M n` for every `n` equals
`filtrationLimit s`. -/
theorem eq_filtrationLimit {s : ℕ → (ReducedTensorWords R M →ₗ[R] P)}
    (hs : ∀ n, ∀ z ∈ filtration R M n, s (n + 1) z = s n z)
    {f : ReducedTensorWords R M →ₗ[R] P}
    (hf : ∀ n, ∀ z ∈ filtration R M n, f z = s n z) : f = filtrationLimit s := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [hf n z hn, filtrationLimit_apply_of_mem_filtration hs hn]

/-- If a stabilising sequence consists of linear maps homogeneous of degree `d`, then its filtration
limit is homogeneous of degree `d`. -/
theorem isHomogeneous_filtrationLimit {G : InternalGrading R M} {Q : ℤ → Submodule R P} {d : ℤ}
    {s : ℕ → (ReducedTensorWords R M →ₗ[R] P)}
    (hs : ∀ n, ∀ z ∈ filtration R M n, s (n + 1) z = s n z)
    (hhom : ∀ n, LinearMap.IsHomogeneous (s n) (gradedPiece G) Q d) :
    LinearMap.IsHomogeneous (filtrationLimit s) (gradedPiece G) Q d := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [filtrationLimit_apply_of_mem_filtration hs hn]
  exact (hhom n).map_mem hz

end FiltrationLimit

/-! ### The contractive biderivation step operator -/

section BiderivStep

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- One step of the recursive expansion of a biderivation `S` with vanishing letter component
satisfying `Δ ∘ S = (S ⊗ F'' + (D₁ ∘ τ) ⊗ D₂ + F ⊗ S) ∘ Δ`: a word of length `n` splits off a
nonempty first block of `d < n` letters, collapsed to a single letter either by `π ∘ F` (with `S`
applied to the remaining `n - d` letters) or by `π ∘ D₁ ∘ τ` (with `D₂` applied to the remaining
`n - d` letters).  Because `0 < d`, both `S` and `D₂` are evaluated only on strictly shorter
words. -/
private noncomputable def biderivStep (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    ∑ d : Fin n.1, if h : 0 < d.1 then
      TensorProduct.lift (
        (prepend R N).compl₁₂
          (letter R N ∘ₗ F ∘ₗ of R M ⟨d.1, h⟩)
          (S ∘ₗ of R M ⟨n.1 - d.1, Nat.sub_pos_of_lt d.2⟩) +
        (prepend R N).compl₁₂
          (letter R N ∘ₗ D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
            of R M ⟨d.1, h⟩)
          (D₂ ∘ₗ of R M ⟨n.1 - d.1, Nat.sub_pos_of_lt d.2⟩)) ∘ₗ
        TensorPower.splitAt R M n.1 d.1 d.2.le
      else 0

/-- Evaluation of `biderivStep` on a pure tensor word. -/
private theorem biderivStep_of_tprod (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    biderivStep G q F D₁ S D₂ (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ∑ d ∈ Finset.range n,
        (prepend R N (letter R N (F (subword R x 0 d))) (S (subword R x d (n - d))) +
          prepend R N
            (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x 0 d))))
            (D₂ (subword R x d (n - d)))) := by
  rw [biderivStep, toModule_of]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · rw [dite_eq_right (by omega), hd, subword_length_zero]
    simp only [map_zero, LinearMap.zero_apply, add_zero]
  · have _ := d.isLt
    rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
      subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega)]
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
      TensorProduct.lift.tmul, LinearMap.add_apply, LinearMap.compl₁₂_apply]
    have hfirst : of R M ⟨d.1, hd⟩
        (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x (Fin.castLE d.isLt.le i)) =
        of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun j : Fin d.1 ↦ x ⟨0 + j.1, by omega⟩) :=
      of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [hfirst]

/-- Evaluation of `biderivStep` on a block of a tensor word. -/
private theorem biderivStep_subword (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    biderivStep G q F D₁ S D₂ (subword R x a b) =
      ∑ d ∈ Finset.range b,
        (prepend R N (letter R N (F (subword R x a d))) (S (subword R x (a + d) (b - d))) +
          prepend R N
            (letter R N (D₁ (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x a d))))
            (D₂ (subword R x (a + d) (b - d)))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j hj ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (biderivStep G q F D₁ S D₂) (subword_eq_of_tprod R x hb hab)
    rw [hx, biderivStep_of_tprod G q F D₁ S D₂ hb]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 h with hb | hab
      · have hb0 : b = 0 := by omega
        rw [hb0, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 h with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (b := b - d) (by omega)]
      simp only [map_zero, add_zero]

/-- Every summand of `biderivStep` has length at least `2`, so its letter component vanishes. -/
private theorem letter_comp_biderivStep (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    letter R N ∘ₗ biderivStep G q F D₁ S D₂ = 0 := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, biderivStep_of_tprod, map_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [map_add, letter_prepend, letter_prepend, add_zero]

/-- On single letters, `biderivStep` vanishes: no nonempty proper prefix exists. -/
private theorem biderivStep_comp_ofLetter (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    biderivStep G q F D₁ S D₂ ∘ₗ ofLetter R M = 0 := by
  refine LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, ← subword_one R M (fun _ : Fin 1 ↦ a) Nat.one_pos,
    biderivStep_subword, Finset.sum_range_one, subword_length_zero]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

/-- On the words of length at most one, `biderivStep` vanishes. -/
private theorem biderivStep_apply_eq_zero_of_mem_filtration_one (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    biderivStep G q F D₁ S D₂ z = 0 :=
  apply_eq_zero_of_mem_filtration_one R M (biderivStep_comp_ofLetter G q F D₁ S D₂) z hz

/-- Contractivity of `biderivStep`: if `S = S'` and `D₂ = D₂'` on `filtration R M n`, then
`biderivStep G q F D₁ S D₂` and `biderivStep G q F D₁ S' D₂'` agree on `filtration R M (n + 1)`. -/
private theorem biderivStep_congr_of_mem_filtration (G : InternalGrading R M) (q : ℤ)
    (F D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {S S' D₂ D₂' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {n : ℕ}
    (hS : ∀ w ∈ filtration R M n, S w = S' w)
    (hD₂ : ∀ w ∈ filtration R M n, D₂ w = D₂' w)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    biderivStep G q F D₁ S D₂ z = biderivStep G q F D₁ S' D₂' z := by
  have h : filtration R M (n + 1) ≤
      LinearMap.eqLocus (biderivStep G q F D₁ S D₂) (biderivStep G q F D₁ S' D₂') := by
    rw [filtration_le_iff]
    rintro ⟨b, hb0⟩ hk _ ⟨w, rfl⟩
    dsimp only at hk w ⊢
    rw [LinearMap.mem_eqLocus]
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
        rw [map_smul, map_smul, map_smul,
          biderivStep_of_tprod G q F D₁ S D₂ hb0, biderivStep_of_tprod G q F D₁ S' D₂' hb0]
        congr 1
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
        · have hmem : subword R x d (b - d) ∈ filtration R M n :=
            subword_mem_filtration R M x d (by omega)
          rw [hS _ hmem, hD₂ _ hmem]
    | add u v hu hv =>
        rw [map_add, map_add, map_add, hu, hv]
  exact h hz

/-- Homogeneity of `biderivStep`: if `F` has degree `0`, `D₁` and `D₂` have degree `-1`, and `S`
has degree `-2`, then `biderivStep G q F D₁ S D₂` has degree `-2`. -/
private theorem isHomogeneous_biderivStep {G : InternalGrading R M} {H : InternalGrading R N}
    (q : ℤ) {F D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hS : LinearMap.IsHomogeneous S (gradedPiece G) (gradedPiece H) (-2))
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (biderivStep G q F D₁ S D₂) (gradedPiece G) (gradedPiece H) (-2) := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ biderivStep G q F D₁ S D₂ w ∈ gradedPiece H (D + -2)) hz ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    rw [biderivStep_of_tprod]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
      exact zero_mem _
    · have hsum : (∑ j ∈ Finset.range d, g j) + ∑ j ∈ Finset.range (n - d), g (d + j) = D := by
        have h1 : ∑ j ∈ Finset.range n, g j = D := by
          rw [← hD, ← Fin.sum_univ_eq_sum_range g n]
          exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
        rw [← h1, ← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
      have hB₁ : subword R x 0 d ∈ gradedPiece G (∑ j ∈ Finset.range d, g j) := by
        simpa only [Nat.zero_add] using subword_mem_gradedPiece x g hxg 0 d (by omega)
      have hB₂ : subword R x d (n - d) ∈ gradedPiece G (∑ j ∈ Finset.range (n - d), g (d + j)) :=
        subword_mem_gradedPiece x g hxg d (n - d) (by omega)
      have hτB₁ : ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x 0 d) ∈
          gradedPiece G (∑ j ∈ Finset.range d, g j) := by
        rw [map_koszulTwist_apply_of_mem G hB₁ q]
        exact Submodule.smul_mem _ _ hB₁
      refine add_mem ?_ ?_
      · have hdeg : D + -2 =
            (∑ j ∈ Finset.range d, g j) + ((∑ j ∈ Finset.range (n - d), g (d + j)) + -2) := by
          omega
        rw [hdeg]
        refine prepend_mem_gradedPiece ?_ (hS.map_mem hB₂)
        simpa only [add_zero] using (isHomogeneous_letter H).map_mem (hF.map_mem hB₁)
      · have hdeg : D + -2 =
            ((∑ j ∈ Finset.range d, g j) + -1) +
              ((∑ j ∈ Finset.range (n - d), g (d + j)) + -1) := by
          omega
        rw [hdeg]
        refine prepend_mem_gradedPiece ?_ (hD₂.map_mem hB₂)
        simpa only [add_zero] using (isHomogeneous_letter H).map_mem (hD₁.map_mem hτB₁)
  · rw [map_zero]
    exact zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- Precomposing an `(F, F')`-coderivation with its own involutive Koszul twist `τ` produces an
`(F ∘ τ, F' ∘ τ)`-coderivation. -/
private theorem isGradedCoderivationAlong_comp_koszulTwist {G : InternalGrading R M} {q : ℤ}
    {F F' D₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁) :
    let τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
    IsGradedCoderivationAlong G q (F ∘ₗ τ) (F' ∘ₗ τ) (D₁ ∘ₗ τ) := by
  intro τ
  have hτ : IsCoalgHom R τ := isCoalgHom_map (G.koszulTwist q)
  have hττ : τ ∘ₗ τ = LinearMap.id := by
    dsimp only [τ]
    rw [← ReducedTensorWords.map_comp, InternalGrading.koszulTwist_comp_self,
      ReducedTensorWords.map_id]
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [hD₁.deconcatenation_apply, hτ.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      have hu : map R (G.koszulTwist q) (map R (G.koszulTwist q) u) = u := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply, τ] using LinearMap.congr_fun hττ u
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply, τ, hu]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- Helper rewriting `TensorProduct.map f g (LinearMap.rTensor _ h w)` as
`TensorProduct.map (f ∘ₗ h) g w`. -/
private theorem map_rTensor_eq
    (f h : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {K : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (w : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    TensorProduct.map f h (LinearMap.rTensor (ReducedTensorWords R M) K w) =
      TensorProduct.map (f ∘ₗ K) h w := by
  rw [LinearMap.rTensor_def, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]

/-- **Inductive deconcatenation step for a fixed point of `biderivStep`.**
Suppose `S = biderivStep G q F D₁ S D₂`, `F` and `F'` are coalgebra morphisms, and `D₁` is a
coderivation along `F` and `F'`.  If on `filtration R M n` both `S` satisfies the `(F, F''; D₁, D₂)`
biderivation rule and `D₂` satisfies the `(F', F'')`-coderivation rule, then `S` satisfies the
`(F, F''; D₁, D₂)` biderivation rule on `filtration R M (n + 1)`. -/
private theorem deconcatenation_biderivStep_of_mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F F' F'' D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hS_fix : S = biderivStep G q F D₁ S D₂)
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD₁ : IsGradedCoderivationAlong G q F F' D₁) {n : ℕ}
    (ihS : ∀ w ∈ filtration R M n,
      deconcatenation R N (S w) =
        TensorProduct.map S F'' (deconcatenation R M w) +
          TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂
            (deconcatenation R M w) +
          TensorProduct.map F S (deconcatenation R M w))
    (ihD₂ : ∀ w ∈ filtration R M n,
      deconcatenation R N (D₂ w) =
        TensorProduct.map D₂ F'' (deconcatenation R M w) +
          TensorProduct.map (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂
            (deconcatenation R M w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N (S z) =
      TensorProduct.map S F'' (deconcatenation R M z) +
        TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂
          (deconcatenation R M z) +
        TensorProduct.map F S (deconcatenation R M z) := by
  let τ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
    ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have hτ : IsCoalgHom R τ := isCoalgHom_map (G.koszulTwist q)
  have hττ : ∀ w, τ (τ w) = w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hFeq : F = coalgHom R (letter R N ∘ₗ F) := hF.eq_coalgHom
  have hF_sub : ∀ {l : ℕ} (x : Fin l → M) (a b : ℕ),
      F (subword R x a b) =
        ofLetter R N (letter R N (F (subword R x a b))) +
          ∑ d ∈ Finset.range b,
            prepend R N (letter R N (F (subword R x a d)))
              (F (subword R x (a + d) (b - d))) := by
    intro l x a b
    conv_lhs => rw [hFeq]
    rw [coalgHom_subword]
    simp only [LinearMap.comp_apply]
    congr 1
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← hFeq]
  have hD₁τ_eq : D₁ ∘ₗ τ =
      gradedCoderivAlong G q (F ∘ₗ τ) (F' ∘ₗ τ) (letter R N ∘ₗ D₁ ∘ₗ τ) :=
    (isGradedCoderivationAlong_comp_koszulTwist hD₁).eq_gradedCoderivAlong
      (hF.comp hτ) (hF'.comp hτ)
  have hD₁τ_sub : ∀ {l : ℕ} (x : Fin l → M) (a b : ℕ),
      D₁ (τ (subword R x a b)) =
        ofLetter R N (letter R N (D₁ (τ (subword R x a b)))) +
          ∑ d ∈ Finset.range b,
            (prepend R N (letter R N (D₁ (τ (subword R x a d))))
                (F' (τ (subword R x (a + d) (b - d)))) +
              prepend R N (letter R N (F (subword R x a d)))
                (D₁ (τ (subword R x (a + d) (b - d))))) := by
    intro l x a b
    rw [← LinearMap.comp_apply D₁ τ]
    conv_lhs => rw [hD₁τ_eq]
    rw [gradedCoderivAlong_subword]
    simp only [LinearMap.comp_apply, τ]
    congr 1
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← hD₁τ_eq]
    simp only [LinearMap.comp_apply, τ, hττ]
  have hS_sub : ∀ {l : ℕ} (x : Fin l → M) (a b : ℕ),
      S (subword R x a b) =
        ∑ d ∈ Finset.range b,
          (prepend R N (letter R N (F (subword R x a d))) (S (subword R x (a + d) (b - d))) +
            prepend R N (letter R N (D₁ (τ (subword R x a d))))
              (D₂ (subword R x (a + d) (b - d)))) := by
    intro l x a b
    conv_lhs => rw [hS_fix]
    exact biderivStep_subword G q F D₁ S D₂ x a b
  have hlocus : filtration R M (n + 1) ≤
      LinearMap.eqLocus (deconcatenation R N ∘ₗ S)
        ((TensorProduct.map S F'' + TensorProduct.map (D₁ ∘ₗ τ) D₂ + TensorProduct.map F S) ∘ₗ
          deconcatenation R M) := by
    rw [filtration_le_iff]
    rintro ⟨b, hb0⟩ hb _ ⟨w, rfl⟩
    dsimp only at hb w ⊢
    rw [LinearMap.mem_eqLocus]
    refine PiTensorProduct.induction_on w (fun r x ↦ ?_) (fun u v hu hv ↦ ?_)
    · simp only [map_smul]
      congr 1
      simp only [LinearMap.comp_apply, LinearMap.add_apply]
      rw [of_tprod_eq_subword R hb0 x]
      have hP₁ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N)
              (prepend R N (letter R N (F (subword R x 0 d))))
              (deconcatenation R N (S (subword R x (0 + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              (prepend R N (letter R N (F (subword R x 0 d)))
                  (S (subword R x (0 + d) c)) ⊗ₜ[R] F'' (subword R x (0 + d + c) (b - d - c)) +
                prepend R N (letter R N (F (subword R x 0 d)))
                  (D₁ (τ (subword R x (0 + d) c))) ⊗ₜ[R]
                  D₂ (subword R x (0 + d + c) (b - d - c)) +
                prepend R N (letter R N (F (subword R x 0 d)))
                  (F (subword R x (0 + d) c)) ⊗ₜ[R] S (subword R x (0 + d + c) (b - d - c))) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
        · rw [ihS _ (subword_mem_filtration R M x (0 + d) (by omega)), map_add, map_add,
            map_deconcatenation_subword, map_deconcatenation_subword, map_deconcatenation_subword,
            map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, τ]
      have hP₂ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N)
              (prepend R N (letter R N (D₁ (τ (subword R x 0 d)))))
              (deconcatenation R N (D₂ (subword R x (0 + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              (prepend R N (letter R N (D₁ (τ (subword R x 0 d))))
                  (D₂ (subword R x (0 + d) c)) ⊗ₜ[R] F'' (subword R x (0 + d + c) (b - d - c)) +
                prepend R N (letter R N (D₁ (τ (subword R x 0 d))))
                  (F' (τ (subword R x (0 + d) c))) ⊗ₜ[R]
                  D₂ (subword R x (0 + d + c) (b - d - c))) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
        · rw [ihD₂ _ (subword_mem_filtration R M x (0 + d) (by omega)), map_add,
            map_deconcatenation_subword, map_deconcatenation_subword, map_sum, map_sum,
            ← Finset.sum_add_distrib]
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, τ]
      conv_lhs => rw [hS_sub]
      rw [map_sum, map_deconcatenation_subword, map_deconcatenation_subword,
        map_deconcatenation_subword]
      simp only [map_add, deconcatenation_prepend]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_congr rfl hP₁, Finset.sum_congr rfl hP₂]
      have hRHS₁ :
          ∑ e ∈ Finset.range b,
              S (subword R x 0 e) ⊗ₜ[R] F'' (subword R x (0 + e) (b - e)) =
            (∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (letter R N (F (subword R x 0 d)))
                    (S (subword R x (0 + d) (e - d))) ⊗ₜ[R]
                  F'' (subword R x (0 + e) (b - e))) +
              ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (letter R N (D₁ (τ (subword R x 0 d))))
                    (D₂ (subword R x (0 + d) (e - d))) ⊗ₜ[R]
                  F'' (subword R x (0 + e) (b - e)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        conv_lhs => rw [hS_sub, TensorProduct.sum_tmul]
        simp only [TensorProduct.add_tmul, Finset.sum_add_distrib]
      have hRHS₂ :
          ∑ e ∈ Finset.range b,
              (D₁ ∘ₗ τ) (subword R x 0 e) ⊗ₜ[R] D₂ (subword R x (0 + e) (b - e)) =
            (∑ e ∈ Finset.range b,
                ofLetter R N (letter R N (D₁ (τ (subword R x 0 e)))) ⊗ₜ[R]
                  D₂ (subword R x (0 + e) (b - e))) +
              ((∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                  prepend R N (letter R N (D₁ (τ (subword R x 0 d))))
                      (F' (τ (subword R x (0 + d) (e - d)))) ⊗ₜ[R]
                    D₂ (subword R x (0 + e) (b - e))) +
                ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                  prepend R N (letter R N (F (subword R x 0 d)))
                      (D₁ (τ (subword R x (0 + d) (e - d)))) ⊗ₜ[R]
                    D₂ (subword R x (0 + e) (b - e))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        conv_lhs => rw [LinearMap.comp_apply, hD₁τ_sub, TensorProduct.add_tmul,
          TensorProduct.sum_tmul]
        simp only [TensorProduct.add_tmul, Finset.sum_add_distrib]
      have hRHS₃ :
          ∑ e ∈ Finset.range b,
              F (subword R x 0 e) ⊗ₜ[R] S (subword R x (0 + e) (b - e)) =
            (∑ e ∈ Finset.range b,
                ofLetter R N (letter R N (F (subword R x 0 e))) ⊗ₜ[R]
                  S (subword R x (0 + e) (b - e))) +
              ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (letter R N (F (subword R x 0 d)))
                    (F (subword R x (0 + d) (e - d))) ⊗ₜ[R]
                  S (subword R x (0 + e) (b - e)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        conv_lhs => rw [hF_sub, TensorProduct.add_tmul, TensorProduct.sum_tmul]
      rw [hRHS₁, hRHS₂, hRHS₃]
      simp only [Finset.sum_add_distrib]
      rw [← Finset.sum_range_diag_flip, ← Finset.sum_range_diag_flip,
        ← Finset.sum_range_diag_flip, ← Finset.sum_range_diag_flip,
        ← Finset.sum_range_diag_flip]
      have hflip : ∀ (u : ℕ → N) (P : ReducedTensorWords R M → ReducedTensorWords R N),
          P 0 = 0 → ∀ (Q : ReducedTensorWords R M → ReducedTensorWords R N),
            ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range (e + 1),
                prepend R N (u d) (P (subword R x (0 + d) (e - d))) ⊗ₜ[R]
                  Q (subword R x (0 + d + (e - d)) (b - d - (e - d))) =
              ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
                prepend R N (u d) (P (subword R x (0 + d) (e - d))) ⊗ₜ[R]
                  Q (subword R x (0 + e) (b - e)) := fun u P hP Q ↦ by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, hP, map_zero,
          TensorProduct.zero_tmul, add_zero]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        have had : 0 + d + (e - d) = 0 + e := by omega
        have hbd : b - d - (e - d) = b - e := by omega
        rw [had, hbd]
      rw [hflip (fun d ↦ letter R N (F (subword R x 0 d))) S (map_zero S) F'',
        hflip (fun d ↦ letter R N (F (subword R x 0 d))) (fun w ↦ D₁ (τ w)) (by simp [τ]) D₂,
        hflip (fun d ↦ letter R N (F (subword R x 0 d))) F (map_zero F) S,
        hflip (fun d ↦ letter R N (D₁ (τ (subword R x 0 d)))) D₂ (map_zero D₂) F'',
        hflip (fun d ↦ letter R N (D₁ (τ (subword R x 0 d)))) (fun w ↦ F' (τ w)) (by simp [τ]) D₂]
      abel
    · rw [map_add, map_add, map_add, hu, hv]
  exact hlocus hz

/-- **Deconcatenation of the graded commutator of a degree-`(-2)` biderivation.**
If `S` satisfies the `(F, F''; D₁, D₂)` biderivation rule at both `z` and `b_M z`, where `b_M` and
`b_N` are degree-one coderivations intertwined by `F` and `F''`, `F` has degree `0`, `D₁` has degree
`-1`, `S` has degree `-2`, `F - F' = b_N ∘ D₁ + D₁ ∘ b_M`, and `F' - F'' = b_N ∘ D₂ + D₂ ∘ b_M`,
then `b_N ∘ S - S ∘ b_M` has deconcatenation equal to its `(F, F'')`-co-Leibniz terms plus the
mismatch `((F - F') ∘ τ) ⊗ D₂ - D₁ ⊗ (F' - F'')`. -/
private theorem deconcatenation_commutator_of_bideriv {G : InternalGrading R M}
    {H : InternalGrading R N}
    {F F' F'' D₁ S D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : IsGradedCoderivation H 1 bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁_hom : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hS_hom : LinearMap.IsHomogeneous S (gradedPiece G) (gradedPiece H) (-2))
    (hFb : bN ∘ₗ F = F ∘ₗ bM)
    (hF''b : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM)
    (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM)
    {z : ReducedTensorWords R M}
    (hSz : deconcatenation R N (S z) =
      TensorProduct.map S F'' (deconcatenation R M z) +
        TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) D₂
          (deconcatenation R M z) +
        TensorProduct.map F S (deconcatenation R M z))
    (hSbMz : deconcatenation R N (S (bM z)) =
      TensorProduct.map S F'' (deconcatenation R M (bM z)) +
        TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) D₂
          (deconcatenation R M (bM z)) +
        TensorProduct.map F S (deconcatenation R M (bM z))) :
    let τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
    deconcatenation R N ((bN ∘ₗ S - S ∘ₗ bM) z) =
      TensorProduct.map (bN ∘ₗ S - S ∘ₗ bM) F'' (deconcatenation R M z) +
        TensorProduct.map (F ∘ₗ τ) (bN ∘ₗ S - S ∘ₗ bM) (deconcatenation R M z) +
        TensorProduct.map ((F - F') ∘ₗ τ) D₂ (deconcatenation R M z) -
        TensorProduct.map D₁ (F' - F'') (deconcatenation R M z) := by
  intro τ
  have hτ_def : τ = ReducedTensorWords.map (R := R) (G.koszulTwist 1) := rfl
  set τN := ReducedTensorWords.map (R := R) (H.koszulTwist 1) with hτN_def
  have hττ : ∀ w, τ (τ w) = w := fun w ↦ by
    rw [← LinearMap.comp_apply, hτ_def, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hτF : ∀ w, τN (F w) = F (τ w) := fun w ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp 1) w
  have hτS : ∀ w, τN (S w) = S (τ w) := fun w ↦ by
    have hpow : ((1 : ℤ) * (-2)).negOnePow = 1 := by decide
    simpa only [hpow, Units.val_one, Int.cast_one, one_smul, LinearMap.comp_apply] using
      LinearMap.congr_fun (hS_hom.map_koszulTwist_comp 1) w
  have hτD₁ : ∀ w, τN (D₁ (τ w)) = - D₁ w := fun w ↦ by
    have hpow : ((1 : ℤ) * (-1)).negOnePow = -1 := by decide
    have h := LinearMap.congr_fun (hD₁_hom.map_koszulTwist_comp 1) (τ w)
    simp only [hpow, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
      LinearMap.comp_apply, LinearMap.smul_apply, ← hτN_def, ← hτ_def] at h
    rw [h, hττ]
  have hτb : ∀ w, τ (bM w) = - bM (τ w) := fun w ↦ by
    have hpow : ((1 : ℤ) * 1).negOnePow = -1 := by decide
    have h := LinearMap.congr_fun (hbM₁.map_koszulTwist_comp 1) w
    simp only [hpow, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
      LinearMap.comp_apply, LinearMap.smul_apply] at h
    exact h
  have hFb' : ∀ w, bN (F w) = F (bM w) := LinearMap.congr_fun hFb
  have hF''b' : ∀ w, bN (F'' w) = F'' (bM w) := LinearMap.congr_fun hF''b
  have hD₁_eq' : ∀ w, bN (D₁ w) + D₁ (bM w) = F w - F' w := fun w ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] using
      (LinearMap.congr_fun hD₁_eq w).symm
  have hD₂_eq' : ∀ w, bN (D₂ w) + D₂ (bM w) = F' w - F'' w := fun w ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] using
      (LinearMap.congr_fun hD₂_eq w).symm
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hbN.deconcatenation_apply, hSz, hSbMz, hbM.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [map_add, TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.comp_apply, LinearMap.sub_apply, ← hτN_def, ← hτ_def]
      simp only [hτF, hτS, hτD₁, hτb, hττ, hFb', hF''b', map_neg, TensorProduct.neg_tmul,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      have eq1 : bN (D₁ (τ u)) ⊗ₜ[R] D₂ v + D₁ (bM (τ u)) ⊗ₜ[R] D₂ v =
          F (τ u) ⊗ₜ[R] D₂ v - F' (τ u) ⊗ₜ[R] D₂ v := by
        rw [← TensorProduct.add_tmul, hD₁_eq', TensorProduct.sub_tmul]
      have eq2 : D₁ u ⊗ₜ[R] bN (D₂ v) + D₁ u ⊗ₜ[R] D₂ (bM v) =
          D₁ u ⊗ₜ[R] F' v - D₁ u ⊗ₜ[R] F'' v := by
        rw [← TensorProduct.tmul_add, hD₂_eq', TensorProduct.tmul_sub]
      calc _ =
          (bN (S u) ⊗ₜ[R] F'' v - S (bM u) ⊗ₜ[R] F'' v) +
          (F (τ u) ⊗ₜ[R] bN (S v) - F (τ u) ⊗ₜ[R] S (bM v)) +
          (bN (D₁ (τ u)) ⊗ₜ[R] D₂ v + D₁ (bM (τ u)) ⊗ₜ[R] D₂ v) -
          (D₁ u ⊗ₜ[R] bN (D₂ v) + D₁ u ⊗ₜ[R] D₂ (bM v)) := by abel
        _ = _ := by rw [eq1, eq2]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

end BiderivStep

/-! ### Transitivity of coderivation homotopies -/

section Trans

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The sequence of approximations to the degree-`(-2)` biderivation correcting `D₁ + D₂`. -/
private noncomputable def transSeq (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ℕ → (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
  | 0 => 0
  | n + 1 => biderivStep G 1 F D₁ (transSeq G F D₁ D₂ n) D₂

private theorem transSeq_stabilises (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ∀ n, ∀ z ∈ filtration R M n, transSeq G F D₁ D₂ (n + 1) z = transSeq G F D₁ D₂ n z
  | 0, z, hz => apply_eq_zero_of_mem_filtration_zero R M _ z hz
  | n + 1, _, hz =>
    biderivStep_congr_of_mem_filtration G 1 F D₁ (transSeq_stabilises G F D₁ D₂ n)
      (fun _ _ ↦ rfl) hz

/-- The degree-`(-2)` biderivation correcting `D₁ + D₂`. -/
private noncomputable def transBideriv (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  filtrationLimit (transSeq G F D₁ D₂)

private theorem transBideriv_fix (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    transBideriv G F D₁ D₂ = biderivStep G 1 F D₁ (transBideriv G F D₁ D₂) D₂ := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  have hn1 : z ∈ filtration R M (n + 1) := filtration_monotone R M (Nat.le_succ n) hn
  rw [transBideriv, filtrationLimit_apply_of_mem_filtration (transSeq_stabilises G F D₁ D₂) hn1,
    transSeq]
  exact biderivStep_congr_of_mem_filtration G 1 F D₁
    (fun w hw ↦ (filtrationLimit_apply_of_mem_filtration
      (transSeq_stabilises G F D₁ D₂) hw).symm)
    (fun _ _ ↦ rfl) hn1

private theorem isHomogeneous_transBideriv {G : InternalGrading R M} {H : InternalGrading R N}
    {F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (transBideriv G F D₁ D₂) (gradedPiece G) (gradedPiece H) (-2) := by
  refine isHomogeneous_filtrationLimit (transSeq_stabilises G F D₁ D₂) fun n ↦ ?_
  induction n with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ n ih => exact isHomogeneous_biderivStep 1 hF₀ hD₁ ih hD₂

/-- **Composition of coderivation homotopies.**
Given an `(F, F')`-coderivation homotopy `D₁` and an `(F', F'')`-coderivation homotopy `D₂`
between coalgebra morphisms intertwining square-zero degree-one coderivations `b_M` and `b_N`,
`homotopyTrans G F D₁ D₂ bM bN` is the `(F, F'')`-coderivation homotopy
`D₁ + D₂ + (b_N ∘ S - S ∘ b_M)`, where `S` is the unique degree-`(-2)` `(F, F''; D₁, D₂)`
biderivation with zero letter component. -/
noncomputable def homotopyTrans (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  D₁ + D₂ + (bN ∘ₗ transBideriv G F D₁ D₂ - transBideriv G F D₁ D₂ ∘ₗ bM)

/-- `homotopyTrans` agrees with `D₁ + D₂` on the words of length at most one, because its higher
biderivation correction vanishes there and `b_M` preserves word length. -/
theorem homotopyTrans_apply_of_mem_filtration_one {G : InternalGrading R M} {q : ℤ}
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G q bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    homotopyTrans G F D₁ D₂ bM bN z = D₁ z + D₂ z := by
  have hS : ∀ w ∈ filtration R M 1, transBideriv G F D₁ D₂ w = 0 := fun w hw ↦ by
    rw [transBideriv_fix]
    exact biderivStep_apply_eq_zero_of_mem_filtration_one G 1 F D₁ _ D₂ hw
  simp only [homotopyTrans, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    hS z hz, hS (bM z) (hbM.mem_filtration hz), map_zero, sub_zero, add_zero]

/-- On single letters, `homotopyTrans` is `D₁ + D₂`. -/
@[simp]
theorem homotopyTrans_ofLetter {G : InternalGrading R M}
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) (a : M) :
    homotopyTrans G F D₁ D₂ bM bN (ofLetter R M a) =
      D₁ (ofLetter R M a) + D₂ (ofLetter R M a) :=
  homotopyTrans_apply_of_mem_filtration_one F D₁ D₂ hbM bN (ofLetter_mem_filtration R M a)

/-- `homotopyTrans` is homogeneous of degree `-1`. -/
theorem isHomogeneous_homotopyTrans {G : InternalGrading R M} {H : InternalGrading R N}
    {F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1))
    (hbM : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) :
    LinearMap.IsHomogeneous (homotopyTrans G F D₁ D₂ bM bN)
      (gradedPiece G) (gradedPiece H) (-1) := by
  have hS := isHomogeneous_transBideriv hF₀ hD₁ hD₂
  have h1 : LinearMap.IsHomogeneous (bN ∘ₗ transBideriv G F D₁ D₂)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa using hbN.comp hS
  have h2 : LinearMap.IsHomogeneous (transBideriv G F D₁ D₂ ∘ₗ bM)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa using hS.comp hbM
  exact (hD₁.add hD₂).add (h1.sub h2)

/-- `homotopyTrans` satisfies the homotopy equation `F - F'' = b_N ∘ D + D ∘ b_M` whenever `b_M`
and `b_N` square to zero. -/
theorem homotopyTrans_eq {G : InternalGrading R M}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM)
    (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM) :
    F - F'' = bN ∘ₗ homotopyTrans G F D₁ D₂ bM bN + homotopyTrans G F D₁ D₂ bM bN ∘ₗ bM := by
  refine LinearMap.ext fun z ↦ ?_
  have hd₁ := LinearMap.congr_fun hD₁_eq z
  have hd₂ := LinearMap.congr_fun hD₂_eq z
  have hbm : bM (bM z) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbM_sq z
  have hbn : ∀ w, bN (bN w) = 0 := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbN_sq w
  simp only [homotopyTrans, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add, map_sub, hbm, hbn, map_zero] at hd₁ hd₂ ⊢
  calc F z - F'' z = (F z - F' z) + (F' z - F'' z) := by abel
    _ = _ := by rw [hd₁, hd₂]; abel

/-- `homotopyTrans` is a `1`-twisted coderivation along `F` and `F''`. -/
theorem isGradedCoderivationAlong_homotopyTrans {G : InternalGrading R M}
    {H : InternalGrading R N}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : IsGradedCoderivation H 1 bN)
    (hFb : bN ∘ₗ F = F ∘ₗ bM) (hF''b : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hD₁ : IsGradedCoderivationAlong G 1 F F' D₁)
    (hD₁_hom : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM)
    (hD₂ : IsGradedCoderivationAlong G 1 F' F'' D₂)
    (hD₂_hom : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1))
    (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F F'' (homotopyTrans G F D₁ D₂ bM bN) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1) with hτ_def
  set S := transBideriv G F D₁ D₂
  have hS_bideriv : ∀ n : ℕ, ∀ w ∈ filtration R M n,
      deconcatenation R N (S w) =
        TensorProduct.map S F'' (deconcatenation R M w) +
          TensorProduct.map (D₁ ∘ₗ τ) D₂ (deconcatenation R M w) +
          TensorProduct.map F S (deconcatenation R M w) := by
    intro n
    induction n with
    | zero =>
        intro w hw
        rw [filtration_zero, Submodule.mem_bot] at hw
        simp [hw]
    | succ n ih =>
        intro w hw
        exact deconcatenation_biderivStep_of_mem_filtration
          (transBideriv_fix G F D₁ D₂) hF hF' hD₁ ih
          (fun u _ ↦ by
            rw [hD₂.deconcatenation_apply, map_rTensor_eq]) hw
  have hS_global : ∀ w,
      deconcatenation R N (S w) =
        TensorProduct.map S F'' (deconcatenation R M w) +
          TensorProduct.map (D₁ ∘ₗ τ) D₂ (deconcatenation R M w) +
          TensorProduct.map F S (deconcatenation R M w) := fun w ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R M w
    exact hS_bideriv n w hn
  have hhom_def : homotopyTrans G F D₁ D₂ bM bN = D₁ + D₂ + (bN ∘ₗ S - S ∘ₗ bM) := rfl
  rw [isGradedCoderivationAlong_iff, hhom_def]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, ← hτ_def]
  rw [map_add, map_add, hD₁.deconcatenation_apply, hD₂.deconcatenation_apply,
    deconcatenation_commutator_of_bideriv hbM hbM₁ hbN hF₀ hD₁_hom
      (isHomogeneous_transBideriv hF₀ hD₁_hom hD₂_hom) hFb hF''b hD₁_eq hD₂_eq
      (hS_global z) (hS_global (bM z))]
  simp only [← hτ_def, map_rTensor_eq]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

end Trans

/-! ### Symmetry of coderivation homotopies -/

section Symm

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The sequence of approximations to the degree-`(-2)` biderivation reversing `D`. -/
private noncomputable def symmSeq (G : InternalGrading R M)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ℕ → (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
  | 0 => 0
  | n + 1 =>
    let Sn := symmSeq G F D bM bN n
    biderivStep G 1 F D Sn (-D - (bN ∘ₗ Sn - Sn ∘ₗ bM))

private theorem symmSeq_stabilises {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ∀ n, ∀ z ∈ filtration R M n,
      symmSeq G F D bM bN (n + 1) z = symmSeq G F D bM bN n z
  | 0, z, hz => apply_eq_zero_of_mem_filtration_zero R M _ z hz
  | n + 1, _, hz => by
    have ih := symmSeq_stabilises F D hbM bN n
    refine biderivStep_congr_of_mem_filtration G 1 F D ih (fun w hw ↦ ?_) hz
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      ih w hw, ih (bM w) (hbM.mem_filtration hw)]

/-- The degree-`(-2)` biderivation reversing `D`. -/
private noncomputable def symmBideriv (G : InternalGrading R M)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  filtrationLimit (symmSeq G F D bM bN)

/-- **Reversal of a coderivation homotopy.**
Given an `(F, F')`-coderivation homotopy `D` between coalgebra morphisms intertwining square-zero
degree-one coderivations `b_M` and `b_N`, `homotopySymm G F D bM bN` is the `(F', F)`-coderivation
homotopy `-D - (b_N ∘ S - S ∘ b_M)`, where `S` solves the coupled biderivation fixed-point
equation `S = biderivStep G 1 F D S (-D - (b_N ∘ S - S ∘ b_M))`. -/
noncomputable def homotopySymm (G : InternalGrading R M)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  -D - (bN ∘ₗ symmBideriv G F D bM bN - symmBideriv G F D bM bN ∘ₗ bM)

private theorem symmBideriv_fix {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    symmBideriv G F D bM bN =
      biderivStep G 1 F D (symmBideriv G F D bM bN) (homotopySymm G F D bM bN) := by
  have hstab := symmSeq_stabilises F D hbM bN
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  have hn1 : z ∈ filtration R M (n + 1) := filtration_monotone R M (Nat.le_succ n) hn
  rw [symmBideriv, filtrationLimit_apply_of_mem_filtration hstab hn1, symmSeq]
  refine biderivStep_congr_of_mem_filtration G 1 F D
    (fun w hw ↦ (filtrationLimit_apply_of_mem_filtration hstab hw).symm)
    (fun w hw ↦ ?_) hn1
  simp only [homotopySymm, symmBideriv, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, filtrationLimit_apply_of_mem_filtration hstab hw,
    filtrationLimit_apply_of_mem_filtration hstab (hbM.mem_filtration hw)]

private theorem isHomogeneous_symmBideriv {G : InternalGrading R M} {H : InternalGrading R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN₁ : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) :
    LinearMap.IsHomogeneous (symmBideriv G F D bM bN) (gradedPiece G) (gradedPiece H) (-2) := by
  refine isHomogeneous_filtrationLimit (symmSeq_stabilises F D hbM bN) fun n ↦ ?_
  induction n with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ n ih =>
      have h1 : LinearMap.IsHomogeneous (bN ∘ₗ symmSeq G F D bM bN n)
          (gradedPiece G) (gradedPiece H) (-1) := by
        simpa using hbN₁.comp ih
      have h2 : LinearMap.IsHomogeneous (symmSeq G F D bM bN n ∘ₗ bM)
          (gradedPiece G) (gradedPiece H) (-1) := by
        simpa using ih.comp hbM₁
      exact isHomogeneous_biderivStep 1 hF₀ hD ih (hD.neg.sub (h1.sub h2))

/-- `homotopySymm` agrees with `-D` on the words of length at most one, because its higher
biderivation correction vanishes there and `b_M` preserves word length. -/
theorem homotopySymm_apply_of_mem_filtration_one {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    homotopySymm G F D bM bN z = -D z := by
  have hS : ∀ w ∈ filtration R M 1, symmBideriv G F D bM bN w = 0 := fun w hw ↦ by
    rw [symmBideriv_fix F D hbM bN]
    exact biderivStep_apply_eq_zero_of_mem_filtration_one G 1 F D _ _ hw
  simp only [homotopySymm, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    hS z hz, hS (bM z) (hbM.mem_filtration hz), map_zero, sub_zero]

/-- On single letters, `homotopySymm` is `-D`. -/
@[simp]
theorem homotopySymm_ofLetter {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) (a : M) :
    homotopySymm G F D bM bN (ofLetter R M a) = -D (ofLetter R M a) :=
  homotopySymm_apply_of_mem_filtration_one F D hbM bN (ofLetter_mem_filtration R M a)

/-- `homotopySymm` is homogeneous of degree `-1`. -/
theorem isHomogeneous_homotopySymm {G : InternalGrading R M} {H : InternalGrading R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN₁ : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) :
    LinearMap.IsHomogeneous (homotopySymm G F D bM bN)
      (gradedPiece G) (gradedPiece H) (-1) := by
  have hS := isHomogeneous_symmBideriv hbM hF₀ hD hbM₁ hbN₁
  have h1 : LinearMap.IsHomogeneous (bN ∘ₗ symmBideriv G F D bM bN)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa using hbN₁.comp hS
  have h2 : LinearMap.IsHomogeneous (symmBideriv G F D bM bN ∘ₗ bM)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa using hS.comp hbM₁
  exact hD.neg.sub (h1.sub h2)

/-- `homotopySymm` satisfies the reversed homotopy equation `F' - F = b_N ∘ D' + D' ∘ b_M`
whenever `b_M` and `b_N` square to zero. -/
theorem homotopySymm_eq {G : InternalGrading R M}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    F' - F = bN ∘ₗ homotopySymm G F D bM bN + homotopySymm G F D bM bN ∘ₗ bM := by
  refine LinearMap.ext fun z ↦ ?_
  have hd := LinearMap.congr_fun hD_eq z
  have hbm : bM (bM z) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbM_sq z
  have hbn : ∀ w, bN (bN w) = 0 := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbN_sq w
  simp only [homotopySymm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, map_sub, map_neg, hbm, hbn, map_zero] at hd ⊢
  calc F' z - F z = -(F z - F' z) := by abel
    _ = _ := by rw [hd]; abel

/-- `homotopySymm` is a `1`-twisted coderivation along `F'` and `F`. -/
theorem isGradedCoderivationAlong_homotopySymm {G : InternalGrading R M}
    {H : InternalGrading R N}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbM_sq : bM ∘ₗ bM = 0)
    (hbN : IsGradedCoderivation H 1 bN)
    (hbN₁ : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1)
    (hbN_sq : bN ∘ₗ bN = 0)
    (hFb : bN ∘ₗ F = F ∘ₗ bM)
    (hD : IsGradedCoderivationAlong G 1 F F' D)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F' F (homotopySymm G F D bM bN) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1) with hτ_def
  set S := symmBideriv G F D bM bN
  set M' := homotopySymm G F D bM bN
  have hM'_unfold : M' = -D - (bN ∘ₗ S - S ∘ₗ bM) := rfl
  have hM'_eq : F' - F = bN ∘ₗ M' + M' ∘ₗ bM := homotopySymm_eq hbM_sq hbN_sq hD_eq
  have hS_hom : LinearMap.IsHomogeneous S (gradedPiece G) (gradedPiece H) (-2) :=
    isHomogeneous_symmBideriv hbM hF₀ hD_hom hbM₁ hbN₁
  -- Simultaneously prove the `(F, F; D, M')`-biderivation rule for `S` and the
  -- `(F', F)`-coderivation rule for `M'` by induction along the conilpotence filtration.
  have hcoupled : ∀ n : ℕ,
      (∀ w ∈ filtration R M n,
        deconcatenation R N (S w) =
          TensorProduct.map S F (deconcatenation R M w) +
            TensorProduct.map (D ∘ₗ τ) M' (deconcatenation R M w) +
            TensorProduct.map F S (deconcatenation R M w)) ∧
      (∀ w ∈ filtration R M n,
        deconcatenation R N (M' w) =
          TensorProduct.map M' F (deconcatenation R M w) +
            TensorProduct.map (F' ∘ₗ τ) M' (deconcatenation R M w)) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩ <;>
        · rw [filtration_zero, Submodule.mem_bot] at hw
          simp [hw]
    | succ n ih =>
        have hS_succ : ∀ w ∈ filtration R M (n + 1),
            deconcatenation R N (S w) =
              TensorProduct.map S F (deconcatenation R M w) +
                TensorProduct.map (D ∘ₗ τ) M' (deconcatenation R M w) +
                TensorProduct.map F S (deconcatenation R M w) :=
          fun w hw ↦ deconcatenation_biderivStep_of_mem_filtration
            (symmBideriv_fix F D hbM bN) hF hF' hD ih.1 ih.2 hw
        refine ⟨hS_succ, fun z hz ↦ ?_⟩
        rw [hM'_unfold, LinearMap.sub_apply, LinearMap.neg_apply, map_sub, map_neg,
          hD.deconcatenation_apply,
          deconcatenation_commutator_of_bideriv hbM hbM₁ hbN hF₀ hD_hom hS_hom hFb hFb hD_eq hM'_eq
            (hS_succ z hz) (hS_succ (bM z) (hbM.mem_filtration hz))]
        simp only [← hτ_def, hM'_unfold, map_rTensor_eq]
        induction deconcatenation R M z using TensorProduct.inductionOn with
        | tmul u v =>
            simp only [TensorProduct.map_tmul, LinearMap.sub_apply, LinearMap.neg_apply,
              LinearMap.comp_apply, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
              TensorProduct.sub_tmul, TensorProduct.tmul_sub]
            abel
        | add u v hu hv =>
            simp only [map_add] at hu hv ⊢
            convert congrArg₂ (· + ·) hu hv using 1 <;> abel
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  simp only [LinearMap.comp_apply, LinearMap.add_apply, ← hτ_def, map_rTensor_eq]
  exact (hcoupled n).2 z hn

end Symm

end TauCeti.ReducedTensorWords
