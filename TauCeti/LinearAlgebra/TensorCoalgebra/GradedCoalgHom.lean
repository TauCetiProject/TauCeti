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

Second, for linear maps `F F' : Tᶜ(M) ⟶ Tᶜ(N)`, a *coderivation along* `F` and `F'` with twist
parameter `q` is a linear map `D : Tᶜ(M) ⟶ Tᶜ(N)` satisfying

`Δ ∘ D = (D ⊗ F') ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of `Tᶜ(M)` of parameter `q`.  Such a map is determined by its
letter component, by induction along the conilpotence filtration, whatever `F` and `F'` are.
Coderivations along a pair of maps are stable under composition with coalgebra morphisms on
either side.  Three instances drive the applications: if `F` and `F'` are coalgebra morphisms then
`F - F'` is an untwisted coderivation along `F` and `F'`; if `F` has degree zero and `b_M`, `b_N`
are graded coderivations then `b_N ∘ F` and `F ∘ b_M` are coderivations along `F` and `F`; and if
`D` is an odd coderivation along `F` and `F'`, and both maps intertwine odd coderivations `b_M` and
`b_N`, then `b_N ∘ D + D ∘ b_M` is an untwisted coderivation along `F` and `F'`.  More generally,
if `D` has degree `p` and twist parameter `p`, and `b_M`, `b_N` have degree and twist parameter
one, then the graded commutator `b_N ∘ D - (-1)^p D ∘ b_M` is a coderivation along `F` and `F'`
with twist parameter `p + 1`; this is the differential of the complex of coderivations along `F`
and `F'`.

Hence a degree-zero coalgebra morphism `F` intertwines two `q`-twisted graded coderivations
`b_M` of `Tᶜ(M)` and `b_N` of `Tᶜ(N)` as soon as it does so after projection onto single letters:
`b_N ∘ F = F ∘ b_M` if and only if `π ∘ b_N ∘ F = π ∘ F ∘ b_M`, where `π : Tᶜ(N) ⟶ N` is the
letter projection.  Applied to bar constructions, this is the statement that an `A∞` morphism is
determined by, and may be constructed from, Taylor components satisfying the suspended component
equation.  In the same way, the homotopy equation `F - F' = b_N ∘ D + D ∘ b_M` for an odd
coderivation `D` along coalgebra morphisms holds as soon as it holds on letter components; this
is the component equation of a homotopy between `A∞` morphisms.

## Main definitions

* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong`: the co-Leibniz rule of a coderivation
  along a pair of maps.
* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: the Taylor expansion of a coderivation along
  two coalgebra morphisms from its letter components.

## Main results

* `TauCeti.ReducedTensorWords.isHomogeneous_coalgHom`: the Taylor expansion of degree-zero
  components has degree zero.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.eq_of_letter_comp_eq` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration`: a coderivation
  along a pair of maps is determined by its letter component, and on words of length at most `n` by
  its letter component and the base maps on those words.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong`, and
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: `gradedCoderivAlong` builds a
  homogeneous coderivation along two coalgebra morphisms with prescribed letter components, and
  `TauCeti.ReducedTensorWords.gradedCoderivAlong_add_apply_of_mem_filtration_succ` describes how
  perturbing its letter components above length `n` shifts it on length `n + 1`.
* `TauCeti.ReducedTensorWords.IsCoalgHom.isGradedCoderivationAlong_sub`: the difference of two
  coalgebra morphisms is a coderivation along them.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp`: the graded
  commutator of a coderivation along a pair of maps with coderivations intertwined by them (and its
  filtered deconcatenation form on a single step of the length filtration).
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.comp_add_comp`: its special case for an
  odd coderivation along a pair of maps and odd coderivations intertwined by them.
* `TauCeti.ReducedTensorWords.IsCoalgHom.comp_eq_comp_iff_letter_comp_eq`: a degree-zero coalgebra
  morphism intertwines two graded coderivations exactly when it does so on letter components.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff`: the homotopy
  equation holds exactly when it holds on letter components.
* `TauCeti.ReducedTensorWords.IsCoalgHom.isHomogeneous_linearEquiv_symm`: the inverse of a
  degree-zero coalgebra automorphism is homogeneous of degree zero.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uL uM uN uP

namespace TauCeti

namespace ReducedTensorWords

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- The Taylor expansion of components of degree zero has degree zero: every word
`f(B₁) ⋯ f(B_k)` it produces from a homogeneous word has the total degree of that word. -/
theorem isHomogeneous_coalgHom {f : ReducedTensorWords R M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous f (gradedPiece G) H.piece 0) :
    LinearMap.IsHomogeneous (coalgHom R f) (gradedPiece G) (gradedPiece H) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero]
  refine gradedPiece_induction (motive := fun w ↦ coalgHom R f w ∈ gradedPiece H D) hz ?_ ?_ ?_
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
          simpa only [add_zero] using hf.map_mem (subword_mem_gradedPiece x g hxg a b)
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
              hf.map_mem (subword_mem_gradedPiece x g hxg a d)
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
      rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact key n 0 (by omega)
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### Coderivations along coalgebra morphisms -/

/-- A *graded coderivation along* `F` and `F'` with twist parameter `q`, also called an
`(F, F')`-coderivation: a linear map `D : Tᶜ(M) ⟶ Tᶜ(N)` satisfying the co-Leibniz rule

`Δ ∘ D = (D ⊗ F') ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

in which `τ = ReducedTensorWords.map (InternalGrading.koszulTwist G q)` is the letterwise Koszul
twist of the source and acts on the left half of every cut.  On a word `z` of homogeneous letters,
summing over the cuts `w₁ ⊗ w₂` of `z`,

`Δ (D z) = ∑ (D w₁ ⊗ F' w₂ + (-1)^(q * |w₁|) • (F w₁ ⊗ D w₂))`.

For `F = F' = id` this is `IsGradedCoderivation G q`.  Homogeneity of `D` is not part of the
condition. -/
def IsGradedCoderivationAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) : Prop :=
  deconcatenation R N ∘ₗ D =
    TensorProduct.map D F' ∘ₗ deconcatenation R M +
      TensorProduct.map F D ∘ₗ
        LinearMap.rTensor (ReducedTensorWords R M)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M

/-- The co-Leibniz identity of a coderivation along a pair of maps, as a reusable `Iff`: this
exposes the body of the predicate to consumers in other modules. -/
theorem isGradedCoderivationAlong_iff {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    IsGradedCoderivationAlong G q F F' D ↔
      deconcatenation R N ∘ₗ D =
        TensorProduct.map D F' ∘ₗ deconcatenation R M +
          TensorProduct.map F D ∘ₗ
            LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M :=
  Iff.rfl

/-- The co-Leibniz identity of a coderivation along a pair of maps, applied to an element. -/
theorem IsGradedCoderivationAlong.deconcatenation_apply {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (z : ReducedTensorWords R M) :
    deconcatenation R N (D z) =
      TensorProduct.map D F' (deconcatenation R M z) +
        TensorProduct.map F D
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) :=
  LinearMap.congr_fun hD z

/-- The coderivations along the identity on both sides are the graded coderivations. -/
theorem isGradedCoderivationAlong_id_id_iff {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsGradedCoderivationAlong G q LinearMap.id LinearMap.id b ↔ IsGradedCoderivation G q b := by
  rw [isGradedCoderivationAlong_iff, isGradedCoderivation_iff, ← LinearMap.rTensor_def,
    ← LinearMap.lTensor_def, LinearMap.comp_assoc]

/-- Two coderivations along pairs of maps that agree on the words of length at most `n`, and whose
letter components agree on those words, agree on those words: the deconcatenation of a word of
length at most `k + 1` only involves words of length at most `k`, which the Koszul twist
preserves. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {q : ℤ}
    {F₁ F'₁ D₁ F₂ F'₂ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F'₁ D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F'₂ D₂) {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F'₁ z = F'₂ z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      simp only [(Submodule.mem_bot R).1 hz, map_zero]
  | succ n ih =>
      have ih' : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun w hw ↦ hF w (filtration_monotone R M n.le_succ hw))
          (fun w hw ↦ hF' w (filtration_monotone R M n.le_succ hw))
          (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
      clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          have hτu : ReducedTensorWords.map (R := R) (G.koszulTwist q) u.1 ∈ filtration R M n :=
            (isCoalgHom_map _).mem_filtration u.2
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul]
          rw [ih' _ u.2, ih' _ v.2, hF _ (filtration_monotone R M n.le_succ hτu),
            hF' _ (filtration_monotone R M n.le_succ v.2)]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- A coderivation along a pair of maps is determined by its letter component: two
coderivations along the same pair of maps whose letter components agree are equal.  This is an
induction along the conilpotence filtration of the source, and it holds for arbitrary `F`
and `F'`. -/
theorem IsGradedCoderivationAlong.eq_of_letter_comp_eq {q : ℤ}
    {F F' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F F' D₁) (h₂ : IsGradedCoderivationAlong G q F F' D₂)
    (hl : letter R N ∘ₗ D₁ = letter R N ∘ₗ D₂) : D₁ = D₂ := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact h₁.apply_eq_of_mem_filtration h₂ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun w _ ↦ LinearMap.congr_fun hl w) hn

/-- If two coderivations along pairs of maps have base maps and letter components agreeing on the
words of length at most `n`, then their values on a word of length at most `n + 1` have the same
deconcatenation. -/
theorem IsGradedCoderivationAlong.deconcatenation_apply_eq_of_mem_filtration_succ {q : ℤ}
    {F₁ F'₁ D₁ F₂ F'₂ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F'₁ D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F'₂ D₂) {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F'₁ z = F'₂ z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N (D₁ z) = deconcatenation R N (D₂ z) := by
  have hD : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
    h₁.apply_eq_of_mem_filtration h₂ hF hF' hl hu
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hτu : ReducedTensorWords.map (R := R) (G.koszulTwist q) u.1 ∈ filtration R M n :=
        (isCoalgHom_map _).mem_filtration u.2
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul]
      rw [hD _ u.2, hD _ v.2, hF _ hτu, hF' _ v.2]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- The zero map is a coderivation along every pair of maps. -/
theorem isGradedCoderivationAlong_zero (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    IsGradedCoderivationAlong G q F F' 0 := by
  rw [isGradedCoderivationAlong_iff, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
    LinearMap.comp_zero, LinearMap.zero_comp, LinearMap.zero_comp, add_zero]

/-- A coderivation along a pair of maps whose letter component vanishes on the words of length at
most `n` vanishes on those words. -/
theorem IsGradedCoderivationAlong.apply_eq_zero_of_mem_filtration {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ z ∈ filtration R M n, letter R N (D z) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D z = 0 :=
  hD.apply_eq_of_mem_filtration (isGradedCoderivationAlong_zero G q F F') (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- A coderivation along a pair of maps whose letter component vanishes on the words of length at
most `n` sends every word of length at most `n + 1` to the single letter given by its letter
component: its deconcatenation vanishes there. -/
theorem IsGradedCoderivationAlong.eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ z ∈ filtration R M n, letter R N (D z) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [hD.deconcatenation_apply_eq_of_mem_filtration_succ (isGradedCoderivationAlong_zero G q F F')
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz,
    LinearMap.zero_apply, map_zero, deconcatenation_ofLetter]

/-! ### Taylor expansion of coderivations along coalgebra morphisms -/

/-- The length-`n` component of the Taylor expansion `gradedCoderivAlong G q F F' φ`: either the
whole word is collapsed to the single letter `φ(x₁ ⋯ xₙ)`, or a nonempty first block `B₁` of `d`
letters is split off to produce `φ(B₁) · F'(rest)` and `((π ∘ F)(τ B₁)) · D(rest)`. -/
private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if h : 0 < n then ofLetter R N ∘ₗ φ ∘ₗ of R M ⟨n, h⟩ else 0) +
      ∑ d : Fin n, if h : 0 < d.1 then
        TensorProduct.lift (
          (prepend R N).compl₁₂ (φ ∘ₗ of R M ⟨d.1, h⟩)
            (F' ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩) +
          (prepend R N).compl₁₂
            ((letter R N ∘ₗ F) ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
              of R M ⟨d.1, h⟩)
            (gradedCoderivAlongComponent G q F F' φ (n - d.1))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
      else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The Taylor expansion of a `q`-twisted coderivation along two coalgebra morphisms `F` and `F'`
with prescribed letter components `φ`: on a word `x₁ ⋯ xₙ` it sums, over all cuts into consecutive
nonempty blocks `B₁ ⋯ B_k` and all indices `1 ≤ i ≤ k`, the words
`f(τ B₁) ⋯ f(τ B_{i-1}) φ(B_i) f'(B_{i+1}) ⋯ f'(B_k)`, where `f` and `f'` are the Taylor
components of `F` and `F'`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    gradedCoderivAlongComponent G q F F' φ n.1

/-- Recursive evaluation of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' φ (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (φ (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          (prepend R N (φ (subword R x 0 d)) (F' (subword R x d (n - d))) +
            prepend R N ((letter R N ∘ₗ F)
                (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x 0 d)))
              (gradedCoderivAlong G q F F' φ (subword R x d (n - d)))) := by
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
    have hx0 : of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun i ↦ x (Fin.castLE d.2.le i)) =
        of R M ⟨d.1, hd⟩ (PiTensorProduct.tprod R fun j : Fin d.1 ↦ x ⟨0 + j.1, by omega⟩) :=
      of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [hx0]

/-- Recursive evaluation of `gradedCoderivAlong` on a block of a tensor word: either the whole
block is collapsed by `φ`, or a nonempty first block of `d` letters is split off either through `φ`
followed by `F'` or through `(π ∘ F) ∘ τ` followed by `gradedCoderivAlong`. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' φ (subword R x a b) =
      ofLetter R N (φ (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          (prepend R N (φ (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
            prepend R N ((letter R N ∘ₗ F)
                (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d)))
              (gradedCoderivAlong G q F F' φ (subword R x (a + d) (b - d)))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j hj ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' φ) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' φ hb, hy 0 b (by omega), Nat.add_zero]
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

/-- The letter component of `gradedCoderivAlong G q F F' φ` is `φ`: every summand split into at
least two blocks has length at least two. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' φ = φ := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add, map_sum,
    letter_ofLetter]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong G q F F' φ` is the single letter given by `φ`. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (φ : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' φ (ofLetter R M a) = ofLetter R N (φ (ofLetter R M a)) := by
  have h := gradedCoderivAlong_subword G q F F' φ (fun _ : Fin 1 ↦ a) 0 1
  rw [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem sum_range_diag_subword {P : Type*} [AddCommMonoid P] {b : ℕ}
    (f : ℕ → ℕ → P) (hf0 : ∀ d, f d 0 = 0) :
    (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d), f d c) =
      ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e, f d (e - d) := by
  rw [← Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_range_succ, Nat.sub_self, hf0, add_zero]

/-- Reindex a triangular sum of prepended subwords across cuts. -/
private theorem sum_prepend_subword_tmul_flip {P : Type*} [AddCommMonoid P] [Module R P]
    (y : ℕ → N) (K : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (L : ReducedTensorWords R M →ₗ[R] P) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
        prepend R N (y d) (K (subword R x (a + d) c)) ⊗ₜ[R]
          L (subword R x (a + d + c) (b - d - c))) =
      ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
        prepend R N (y d) (K (subword R x (a + d) (e - d))) ⊗ₜ[R]
          L (subword R x (a + e) (b - e)) := by
  rw [sum_range_diag_subword _ fun d ↦ by
    rw [subword_length_zero, map_zero, map_zero, TensorProduct.zero_tmul]]
  refine Finset.sum_congr rfl fun e he ↦ Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at he hd
  have had : a + d + (e - d) = a + e := by omega
  have hbd : b - d - (e - d) = b - e := by omega
  rw [had, hbd]

/-- Recursive expansion of a coalgebra morphism after a letterwise map on a subword. -/
private theorem coalgHom_comp_map_subword {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (g : M →ₗ[R] M) {n : ℕ} (x : Fin n → M) (a e : ℕ) :
    (F ∘ₗ ReducedTensorWords.map (R := R) g) (subword R x a e) =
      ofLetter R N ((letter R N ∘ₗ F) (ReducedTensorWords.map (R := R) g (subword R x a e))) +
        ∑ d ∈ Finset.range e,
          prepend R N ((letter R N ∘ₗ F) (ReducedTensorWords.map (R := R) g (subword R x a d)))
            ((F ∘ₗ ReducedTensorWords.map (R := R) g) (subword R x (a + d) (e - d))) := by
  rw [LinearMap.comp_apply]
  nth_rw 1 [hF.eq_coalgHom]
  rw [map_subword, coalgHom_subword]
  simp only [← map_subword, ← hF.eq_coalgHom]
  rfl

private theorem deconcatenation_gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (φ : ReducedTensorWords R M →ₗ[R] N)
    {n : ℕ} (x : Fin n → M) (b a : ℕ) :
    deconcatenation R N (gradedCoderivAlong G q F F' φ (subword R x a b)) =
      TensorProduct.map (gradedCoderivAlong G q F F' φ) F'
          (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
          (gradedCoderivAlong G q F F' φ) (deconcatenation R M (subword R x a b)) := by
  set D := gradedCoderivAlong G q F F' φ
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    have hP₁ : ∀ d ∈ Finset.range b,
        LinearMap.rTensor _ (prepend R N (φ (subword R x a d)))
            (deconcatenation R N (F' (subword R x (a + d) (b - d)))) =
          ∑ c ∈ Finset.range (b - d),
            prepend R N (φ (subword R x a d)) (F' (subword R x (a + d) c)) ⊗ₜ[R]
              F' (subword R x (a + d + c) (b - d - c)) := fun d _ ↦ by
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
          TensorProduct.zero_tmul, Finset.sum_const_zero]
      · rw [hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum]
        simp only [LinearMap.rTensor_tmul]
    have hP₂ : ∀ d ∈ Finset.range b,
        LinearMap.rTensor _ (prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d))))
            (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
          (∑ c ∈ Finset.range (b - d),
              prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
                (D (subword R x (a + d) c)) ⊗ₜ[R] F' (subword R x (a + d + c) (b - d - c))) +
            ∑ c ∈ Finset.range (b - d),
              prepend R N ((letter R N ∘ₗ F) (τ (subword R x a d)))
                ((F ∘ₗ τ) (subword R x (a + d) c)) ⊗ₜ[R]
                  D (subword R x (a + d + c) (b - d - c)) := fun d hd ↦ by
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
          TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero]
      · rw [ih (b - d) (by omega) (a + d), map_add, map_deconcatenation_subword,
          map_deconcatenation_subword, map_sum, map_sum]
        simp only [LinearMap.rTensor_tmul]
    rw [gradedCoderivAlong_subword, map_add, deconcatenation_ofLetter, zero_add, map_sum,
      map_deconcatenation_subword, map_deconcatenation_subword]
    simp only [map_add, deconcatenation_prepend, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl hP₁, Finset.sum_congr rfl hP₂, Finset.sum_add_distrib,
      sum_prepend_subword_tmul_flip, sum_prepend_subword_tmul_flip, sum_prepend_subword_tmul_flip,
      Finset.sum_congr (f := fun e ↦ D (subword R x a e) ⊗ₜ[R] F' (subword R x (a + e) (b - e)))
        rfl (fun e _ ↦ congrArg (· ⊗ₜ[R] F' (subword R x (a + e) (b - e)))
          (gradedCoderivAlong_subword G q F F' φ x a e)),
      Finset.sum_congr
        (f := fun e ↦ (F ∘ₗ τ) (subword R x a e) ⊗ₜ[R] D (subword R x (a + e) (b - e))) rfl
        (fun e _ ↦ congrArg (· ⊗ₜ[R] D (subword R x (a + e) (b - e)))
          (coalgHom_comp_map_subword hF (G.koszulTwist q) x a e))]
    simp only [TensorProduct.add_tmul, TensorProduct.sum_tmul, Finset.sum_add_distrib]
    abel

/-- When `F` and `F'` are coalgebra morphisms, `gradedCoderivAlong G q F F' φ` is a `q`-twisted
coderivation along `F` and `F'`. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (φ : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' φ) := by
  rw [isGradedCoderivationAlong_iff]
  refine linearMap_ext R M fun n x ↦ ?_
  have hr : TensorProduct.map F (gradedCoderivAlong G q F F' φ) ∘ₗ
      LinearMap.rTensor (ReducedTensorWords R M) (ReducedTensorWords.map (R := R) (G.koszulTwist q))
        = TensorProduct.map (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
            (gradedCoderivAlong G q F F' φ) := by
    rw [LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id]
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map F _), hr, of_tprod_eq_subword R n.2]
  exact deconcatenation_gradedCoderivAlong_subword G q hF hF' φ x n.1 0

/-- Every coderivation along two coalgebra morphisms is the Taylor expansion of its letter
component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Total degree of `gradedCoderivAlong` on a homogeneous subword. -/
private theorem gradedCoderivAlong_subword_mem_gradedPiece {q r : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {φ : ReducedTensorWords R M →ₗ[R] N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF' : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece G) H.piece r) {n : ℕ} (x : Fin n → M)
    (g : ℕ → ℤ) (hxg : ∀ i : Fin n, x i ∈ G.piece (g i)) (b a : ℕ) (hab : a + b ≤ n) :
    gradedCoderivAlong G q F F' φ (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := by
  have hτxg : ∀ i : Fin n, G.koszulTwist q (x i) ∈ G.piece (g i) :=
    fun i ↦ G.koszulTwist_mem_piece (hxg i) q
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [gradedCoderivAlong_subword]
    refine add_mem
      (ofLetter_mem_gradedPiece H (hφ.map_mem (subword_mem_gradedPiece x g hxg a b)))
      (Submodule.sum_mem _ fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | _
    · simp only [subword_length_zero, map_zero, add_zero]
      exact zero_mem _
    · have hsplit : ∑ j ∈ Finset.range b, g (a + j) =
          (∑ j ∈ Finset.range d, g (a + j)) +
            ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
        rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
        simp only [Nat.add_assoc]
      refine add_mem ?_ ?_
      · have hdeg : (∑ j ∈ Finset.range b, g (a + j)) + r =
            ((∑ j ∈ Finset.range d, g (a + j)) + r) +
              ∑ j ∈ Finset.range (b - d), g (a + d + j) := by rw [hsplit]; ring
        rw [hdeg]
        refine prepend_mem_gradedPiece (hφ.map_mem (subword_mem_gradedPiece x g hxg a d)) ?_
        simpa only [add_zero] using
          hF'.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d))
      · have hdeg : (∑ j ∈ Finset.range b, g (a + j)) + r =
            (∑ j ∈ Finset.range d, g (a + j)) +
              ((∑ j ∈ Finset.range (b - d), g (a + d + j)) + r) := by rw [hsplit, add_assoc]
        rw [hdeg, map_subword]
        refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
        simpa only [LinearMap.comp_apply, add_zero] using
          (isHomogeneous_letter H).map_mem
            (hF.map_mem (subword_mem_gradedPiece _ g hτxg a d))

/-- If `F` and `F'` have degree zero and `φ` has degree `r`, then `gradedCoderivAlong G q F F' φ`
has degree `r`. -/
theorem isHomogeneous_gradedCoderivAlong {q r : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {φ : ReducedTensorWords R M →ₗ[R] N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF' : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' φ) (gradedPiece G) (gradedPiece H) r := by
  rw [LinearMap.isHomogeneous_def]
  intro E z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' φ w ∈ gradedPiece H (E + r)) hz ?_ ?_ ?_
  · intro n hn 𝒟 x hx hE
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = E := by
      rw [← hE, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact gradedCoderivAlong_subword_mem_gradedPiece hF hF' hφ x g hxg n 0 (by omega)
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- Two `gradedCoderivAlong` expansions along coalgebra morphisms agree on the words of length at
most `n` when their base maps and letter components agree on those words. -/
theorem gradedCoderivAlong_apply_eq_of_mem_filtration {q : ℤ}
    {F₁ F'₁ F₂ F'₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₁ : IsCoalgHom R F₁) (hF'₁ : IsCoalgHom R F'₁)
    (hF₂ : IsCoalgHom R F₂) (hF'₂ : IsCoalgHom R F'₂)
    {φ₁ φ₂ : ReducedTensorWords R M →ₗ[R] N} {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F'₁ z = F'₂ z)
    (hφ : ∀ z ∈ filtration R M n, φ₁ z = φ₂ z)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F₁ F'₁ φ₁ z = gradedCoderivAlong G q F₂ F'₂ φ₂ z :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF₁ hF'₁ φ₁).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF'₂ φ₂) hF hF'
    (fun w hw ↦ by
      rw [← LinearMap.comp_apply (letter R N), ← LinearMap.comp_apply (letter R N),
        letter_comp_gradedCoderivAlong, letter_comp_gradedCoderivAlong, hφ w hw]) hz

/-- Perturbing the letter components of `gradedCoderivAlong` by a map `η` vanishing on the words of
length at most `n`, while changing the coalgebra morphisms only above length `n`, shifts the value
on a word `z` of length at most `n + 1` by the single letter `η z`. -/
theorem gradedCoderivAlong_add_apply_of_mem_filtration_succ {q : ℤ}
    {F₁ F'₁ F₂ F'₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₁ : IsCoalgHom R F₁) (hF'₁ : IsCoalgHom R F'₁)
    (hF₂ : IsCoalgHom R F₂) (hF'₂ : IsCoalgHom R F'₂)
    {φ η : ReducedTensorWords R M →ₗ[R] N} {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F'₁ z = F'₂ z)
    (hη : ∀ z ∈ filtration R M n, η z = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    gradedCoderivAlong G q F₁ F'₁ (φ + η) z =
      gradedCoderivAlong G q F₂ F'₂ φ z + ofLetter R N (η z) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ ?_
  · rw [map_add, deconcatenation_ofLetter, add_zero]
    exact (isGradedCoderivationAlong_gradedCoderivAlong G q hF₁ hF'₁ (φ + η))
      |>.deconcatenation_apply_eq_of_mem_filtration_succ
        (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF'₂ φ) hF hF'
        (fun w hw ↦ by
          rw [← LinearMap.comp_apply (letter R N), ← LinearMap.comp_apply (letter R N),
            letter_comp_gradedCoderivAlong, letter_comp_gradedCoderivAlong, LinearMap.add_apply,
            hη w hw, add_zero]) hz
  · rw [← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong, LinearMap.add_apply,
      map_add, ← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong,
      letter_ofLetter]

/-- The co-Leibniz rule of a coderivation along a pair of maps only depends on the parity of the
twist parameter: negating it changes nothing. -/
@[simp]
theorem isGradedCoderivationAlong_neg_iff {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    IsGradedCoderivationAlong G (-q) F F' D ↔ IsGradedCoderivationAlong G q F F' D := by
  rw [isGradedCoderivationAlong_iff, isGradedCoderivationAlong_iff,
    InternalGrading.koszulTwist_neg]

/-- The sum of two coderivations along the same pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.add {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D + D') := by
  rw [isGradedCoderivationAlong_iff] at hD hD' ⊢
  rw [TensorProduct.map_add_left, TensorProduct.map_add_right, LinearMap.comp_add, hD, hD',
    LinearMap.add_comp, LinearMap.add_comp]
  abel

/-- A scalar multiple of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.smul {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (r : R) :
    IsGradedCoderivationAlong G q F F' (r • D) := by
  rw [isGradedCoderivationAlong_iff] at hD ⊢
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, LinearMap.comp_smul, hD,
    LinearMap.smul_comp, LinearMap.smul_comp, smul_add]

/-- Following a coderivation along `F` and `F'` by a coalgebra morphism `K` gives a coderivation
along `K ∘ F` and `K ∘ F'`. -/
theorem IsCoalgHom.comp_isGradedCoderivationAlong {P : Type uP} [AddCommMonoid P] [Module R P]
    {K : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R P} (hK : IsCoalgHom R K) {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q (K ∘ₗ F) (K ∘ₗ F') (K ∘ₗ D) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [hK.deconcatenation_apply, hD.deconcatenation_apply, map_add, ← LinearMap.comp_apply
    (TensorProduct.map K K), ← TensorProduct.map_comp, ← LinearMap.comp_apply
    (TensorProduct.map K K), ← TensorProduct.map_comp]

/-- Precomposing a coderivation along `F` and `F'` with a degree-zero coalgebra morphism `K`
gives a coderivation along `F ∘ K` and `F' ∘ K`: the morphism commutes with the letterwise Koszul
twists. -/
theorem IsGradedCoderivationAlong.comp_isCoalgHom {L : Type uL} [AddCommMonoid L] [Module R L]
    {E : InternalGrading R L ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    {K : ReducedTensorWords R L →ₗ[R] ReducedTensorWords R M} (hK : IsCoalgHom R K)
    (hK₀ : LinearMap.IsHomogeneous K (gradedPiece E) (gradedPiece G) 0) :
    IsGradedCoderivationAlong E q (F ∘ₗ K) (F' ∘ₗ K) (D ∘ₗ K) := by
  -- A degree-zero map commutes with the letterwise Koszul twists.
  have hτ : ∀ z, ReducedTensorWords.map (R := R) (G.koszulTwist q) (K z) =
      K (ReducedTensorWords.map (R := R) (E.koszulTwist q) z) := fun z ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hK₀.map_koszulTwist_comp q) z
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [hD.deconcatenation_apply, hK.deconcatenation_apply]
  induction deconcatenation R L z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply, hτ]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- A coalgebra morphism `F` followed by a graded coderivation of the target is a coderivation
along `F` and `F`, provided `F` has degree zero. -/
theorem IsGradedCoderivation.comp_isCoalgHom {q : ℤ}
    {b : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N} (hb : IsGradedCoderivation H q b)
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) :
    IsGradedCoderivationAlong G q F F (b ∘ₗ F) := by
  simpa only [LinearMap.id_comp] using
    ((isGradedCoderivationAlong_id_id_iff (G := H)).2 hb).comp_isCoalgHom hF hF₀

/-- A graded coderivation of the source followed by a coalgebra morphism `F` is a coderivation
along `F` and `F`. -/
theorem IsCoalgHom.comp_isGradedCoderivation {q : ℤ}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hb : IsGradedCoderivation G q b) :
    IsGradedCoderivationAlong G q F F (F ∘ₗ b) := by
  simpa only [LinearMap.comp_id] using
    hF.comp_isGradedCoderivationAlong ((isGradedCoderivationAlong_id_id_iff (G := G)).2 hb)

/-! ### Intertwining graded coderivations -/

/-- A degree-zero coalgebra morphism intertwines a `q`-twisted graded coderivation of `Tᶜ(M)`
with one of `Tᶜ(N)` as soon as it does so after projection onto single letters: both composites
are coderivations along `F` and `F`. -/
theorem IsCoalgHom.comp_eq_comp_of_letter_comp_eq
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {q : ℤ}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G q bM) (hbN : IsGradedCoderivation H q bN)
    (hl : letter R N ∘ₗ bN ∘ₗ F = letter R N ∘ₗ F ∘ₗ bM) : bN ∘ₗ F = F ∘ₗ bM :=
  (hbN.comp_isCoalgHom hF hF₀).eq_of_letter_comp_eq (hF.comp_isGradedCoderivation hbM) hl

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

/-! ### Differences of coalgebra morphisms and odd coderivations -/

section Difference

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- The difference of two coalgebra morphisms `F` and `F'` is an untwisted coderivation along `F`
and `F'`: `Δ (F - F') = ((F - F') ⊗ F' + F ⊗ (F - F')) Δ`. -/
theorem IsCoalgHom.isGradedCoderivationAlong_sub
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') : IsGradedCoderivationAlong G 0 F F' (F - F') := by
  rw [isGradedCoderivationAlong_iff, InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id,
    LinearMap.rTensor_id, LinearMap.id_comp]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  rw [hF.deconcatenation_apply, hF'.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.sub_apply, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- The negation of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.neg {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q F F' (-D) := by
  have heq : (-D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) = (-1 : R) • D :=
    LinearMap.ext fun z ↦ by
      rw [LinearMap.neg_apply, LinearMap.smul_apply, neg_one_smul]
  rw [heq]
  exact hD.smul (-1 : R)

/-- The difference of two coderivations along the same pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.sub {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') := by
  have heq : (D - D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) = D + -D' :=
    LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, sub_eq_add_neg]
  rw [heq]
  exact hD.add hD'.neg

/-- Filtered form of `IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp`: when `F` and `F'`
intertwine `b_M` and `b_N` on the words of length at most `n`, the graded commutator
`b_N ∘ D - (-1)^(q r) D ∘ b_M` satisfies the `(t + q)`-twisted co-Leibniz rule on every word of
length at most `n + 1`, because every cut of such a word has both halves (and their Koszul twists)
of length at most `n`. -/
theorem IsGradedCoderivationAlong.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration
    {t q r s : ℤ} {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G t F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (t * s).negOnePow = (q * r).negOnePow)
    (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    {n : ℕ} (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) z) =
      TensorProduct.map (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) F'
          (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM))
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)))
            (deconcatenation R M z)) := by
  set c : R := (((q * r).negOnePow : ℤ) : R) with hc
  have hτF : ∀ w, ReducedTensorWords.map (R := R) (H.koszulTwist q) (F w) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := fun w ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) w
  have hτD : ∀ w, ReducedTensorWords.map (R := R) (H.koszulTwist q) (D w) =
      c • D (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) w
  have hτb : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist t) (bM w) =
      c • bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) w) := fun w ↦ by
    simpa only [hs, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp t) w
  have hττ : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist q)
      (ReducedTensorWords.map (R := R) (G.koszulTwist t) w) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp, add_comm]
  have hττ' : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist t)
      (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp, InternalGrading.koszulTwist_comp]
  have hcc : ∀ x : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N, c • c • x = x := by
    intro x
    rw [smul_smul, hc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_sub, map_smul, hbN.deconcatenation_apply, hD.deconcatenation_apply,
    hD.deconcatenation_apply, hbM.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hFbu : bN (F (ReducedTensorWords.map (R := R) (G.koszulTwist t) u.1)) =
          F (bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) u.1)) :=
        hF _ ((isCoalgHom_map _).mem_filtration u.2)
      have hF'bv : bN (F' v.1) = F' (bM v.1) := hF' _ v.2
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, map_smul,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hτF, hτD, hτb, hττ,
        hττ', hFbu, hF'bv, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
        TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_add, hcc]
      abel
  | add u v hu hv =>
      simp only [map_add, smul_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- Let `D` be a coderivation along `F` and `F'` with twist parameter `t` and of degree `r`, where
`F` has degree zero and both `F` and `F'` intertwine coderivations `b_M` of `Tᶜ(M)` and `b_N` of
`Tᶜ(N)` with twist parameter `q`, with `b_M` of degree `s`.  If `(-1)^(t s) = (-1)^(q r)`, then the
graded commutator `b_N ∘ D - (-1)^(q r) D ∘ b_M` is a coderivation along `F` and `F'` with twist
parameter `t + q`.  On each cut, the cross terms cancel in pairs because `D` commutes with the
twist of parameter `q`, and `b_M` with that of parameter `t`, up to this common sign.  For
transformations of degree `p` this is the differential of the complex of coderivations along `F`
and `F'`. -/
theorem IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp {t q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G t F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (t * s).negOnePow = (q * r).negOnePow)
    (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    IsGradedCoderivationAlong G (t + q) F F'
      (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact hD.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration hD₁ hbM hbM₁ hs hbN hF₀
    (fun w _ ↦ LinearMap.congr_fun hF w) (fun w _ ↦ LinearMap.congr_fun hF' w)
    (filtration_monotone R M n.le_succ hn)

/-- Filtered odd case of `IsGradedCoderivationAlong.comp_add_comp`: when `F` and `F'` intertwine
odd graded coderivations `b_M` and `b_N` on the words of length at most `n`, the anticommutator
`b_N ∘ D + D ∘ b_M` of an odd coderivation `D` along `F` and `F'` satisfies the untwisted
co-Leibniz rule on every word of length at most `n + 1`. -/
theorem IsGradedCoderivationAlong.deconcatenation_comp_add_comp_of_mem_filtration {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    {n : ℕ} (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D + D ∘ₗ bM) z) =
      TensorProduct.map (bN ∘ₗ D + D ∘ₗ bM) F' (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D + D ∘ₗ bM) (deconcatenation R M z) := by
  have h := hD.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration hD₁ hbM hbM₁
    (hs.trans hr.symm) hbN hF₀ hF hF' hz
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun w ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, sub_neg_eq_add]
  have hτ : G.koszulTwist (q + q) = LinearMap.id := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self]
  rwa [he, hτ, ReducedTensorWords.map_id, LinearMap.rTensor_id, LinearMap.id_apply] at h

/-- Let `D` be an odd coderivation along `F` and `F'`, where `F` has degree zero and both `F` and
`F'` intertwine odd graded coderivations `b_M` of `Tᶜ(M)` and `b_N` of `Tᶜ(N)`.  Then
`b_N ∘ D + D ∘ b_M` is an untwisted coderivation along `F` and `F'`.  This is the case of
`IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp` where all twists agree and both signs
are `-1`. -/
theorem IsGradedCoderivationAlong.comp_add_comp {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    IsGradedCoderivationAlong G 0 F F' (bN ∘ₗ D + D ∘ₗ bM) := by
  have h := hD.comp_sub_negOnePow_smul_comp hD₁ hbM hbM₁ (hs.trans hr.symm) hbN hF₀ hF hF'
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, sub_neg_eq_add]
  rw [he] at h
  have hτ : G.koszulTwist (q + q) = G.koszulTwist 0 := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self,
      InternalGrading.koszulTwist_zero]
  rwa [isGradedCoderivationAlong_iff, hτ, ← isGradedCoderivationAlong_iff] at h

/-- **The homotopy equation is determined by its letter component.**  Under the hypotheses of
`IsGradedCoderivationAlong.comp_add_comp`, if `F'` is also a coalgebra morphism, then
`F - F' = b_N ∘ D + D ∘ b_M` holds as soon as it holds after projection onto single letters. -/
theorem IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hFc : IsCoalgHom R F) (hF'c : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    F - F' = bN ∘ₗ D + D ∘ₗ bM ↔
      letter R N ∘ₗ (F - F') = letter R N ∘ₗ (bN ∘ₗ D + D ∘ₗ bM) :=
  ⟨fun h ↦ by rw [h], (hFc.isGradedCoderivationAlong_sub hF'c).eq_of_letter_comp_eq
    (hD.comp_add_comp hD₁ hr hbM hbM₁ hs hbN hF₀ hF hF')⟩

end Difference

/-! ### Inverses -/

section Inverse

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The inverse of a degree-zero linear equivalence of reduced tensor coalgebras which is a
coalgebra morphism is again homogeneous of degree zero. -/
theorem IsCoalgHom.isHomogeneous_linearEquiv_symm {G : InternalGrading R M ℤ}
    {H : InternalGrading R N ℤ} {e : ReducedTensorWords R M ≃ₗ[R] ReducedTensorWords R N}
    (he : IsCoalgHom R e.toLinearMap)
    (he₀ : LinearMap.IsHomogeneous e.toLinearMap (gradedPiece G) (gradedPiece H) 0) :
    LinearMap.IsHomogeneous e.symm.toLinearMap (gradedPiece H) (gradedPiece G) 0 := by
  -- No independence of the total-degree pieces is available, so the inverse is not read off a
  -- decomposition.  Instead `e` is corrected by the letterwise inverse of its arity-one
  -- component `e₁` to a coalgebra endomorphism `U` fixing every letter; `U` preserves each
  -- total-degree piece and, being the identity up to a filtration-lowering map, maps it onto
  -- itself.
  -- The arity-one component `e₁` is a degree-zero linear equivalence of the letters.
  set e₁ : M ≃ₗ[R] N := LinearEquiv.ofBijective _ he.letter_comp_comp_ofLetter_bijective
  have he₁ : LinearMap.IsHomogeneous e₁.toLinearMap G.piece H.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    have h := (isHomogeneous_letter H).map_mem (he₀.map_mem (ofLetter_mem_gradedPiece G ha))
    rw [add_zero, add_zero] at h
    rw [add_zero]
    exact h
  have he₁' := (isHomogeneous_map H G he₁.linearEquiv_symm)
  -- The correction `U` is a degree-zero coalgebra endomorphism fixing every letter.
  set U := ReducedTensorWords.map (R := R) e₁.symm.toLinearMap ∘ₗ e.toLinearMap with hUdef
  have hU : IsCoalgHom R U := (isCoalgHom_map _).comp he
  have hU₁ : U ∘ₗ ofLetter R M = ofLetter R M := he.map_symm_comp_comp_ofLetter _
  have hU₀ := he₁'.comp he₀
  rw [zero_add] at hU₀
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  rw [add_zero]
  have hw' : ReducedTensorWords.map (R := R) e₁.symm.toLinearMap w ∈ gradedPiece G D := by
    simpa only [add_zero] using he₁'.map_mem hw
  have hp : (gradedPiece G D).map U ≤ gradedPiece G D := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [add_zero] using hU₀.map_mem hz
  have hw'' : ReducedTensorWords.map (R := R) e₁.symm.toLinearMap w ∈ (gradedPiece G D).map U := by
    rw [hU.map_eq_of_map_le (p := gradedPiece G D) hU₁ hp]
    exact hw'
  obtain ⟨z, hz, hUz⟩ := hw''
  have hez : e z = w := by
    have h := congrArg (ReducedTensorWords.map (R := R) e₁.toLinearMap) hUz
    rwa [hUdef, LinearMap.comp_apply, map_map_symm, map_map_symm, LinearEquiv.coe_coe] at h
  rw [← hez, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact hz

end Inverse

end ReducedTensorWords

end TauCeti
