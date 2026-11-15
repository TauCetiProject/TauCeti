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
* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: the Taylor expansion of a map from words to
  letters as a `q`-twisted coderivation along a pair of coalgebra morphisms.
* `TauCeti.ReducedTensorWords.stabilisingLimit`: the limit of a sequence of maps out of reduced
  tensor words that stabilises along the conilpotence filtration.

## Main results

* `TauCeti.ReducedTensorWords.isHomogeneous_coalgHom`: the Taylor expansion of degree-zero
  components has degree zero.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.eq_of_letter_comp_eq` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration`: a coderivation
  along a pair of maps is determined by its letter component, globally and on each step of the
  conilpotence filtration.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong`, and
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: existence and homogeneity of a
  coderivation along coalgebra morphisms with prescribed Taylor components.
* `TauCeti.ReducedTensorWords.IsCoalgHom.isGradedCoderivationAlong_sub`: the difference of two
  coalgebra morphisms is a coderivation along them.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp`: the graded
  commutator of a coderivation along a pair of maps with coderivations intertwined by them.
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

/-- Two `q`-twisted coderivations along maps that agree on shorter words agree on the words of
length at most `n` whenever their letter components agree on those words.  Since reduced
deconcatenation sends a word of length at most `m + 1` into pairs of words of length at most `m`,
only the values of the ambient maps on words of length at most `n - 1` enter. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration_of_apply_eq {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ z ∈ filtration R M (n - 1), F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M (n - 1), F₁' z = F₂' z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      simp only [(Submodule.mem_bot R).1 hz, map_zero]
  | succ m ih =>
      have ih' : ∀ u ∈ filtration R M m, D₁ u = D₂ u := fun u hu ↦
        ih (fun w hw ↦ hF w (filtration_monotone R M (by omega) hw))
          (fun w hw ↦ hF' w (filtration_monotone R M (by omega) hw))
          (fun w hw ↦ hl w (filtration_monotone R M m.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M m ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
      clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul]
          rw [ih' _ u.2, ih' _ v.2, hF' _ v.2,
            hF _ ((isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2)]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- Two coderivations along the same pair of maps whose letter components agree on the words of
length at most `n` agree on those words. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {q : ℤ}
    {F F' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F F' D₁) (h₂ : IsGradedCoderivationAlong G q F F' D₂)
    {n : ℕ} (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z :=
  h₁.apply_eq_of_mem_filtration_of_apply_eq h₂ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hl hz

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
  exact h₁.apply_eq_of_mem_filtration h₂ (fun w _ ↦ LinearMap.congr_fun hl w) hn

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
  hD.apply_eq_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
    (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- A coderivation along any pair of maps which vanishes on the words of length at most `n` takes
primitive values on the words of length at most `n + 1`: every cut of such a word has both halves
of length at most `n`, so its deconcatenation vanishes. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hzero : ∀ z ∈ filtration R M n, D z = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (n + 1)) : D z = ofLetter R N (letter R N (D z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [deconcatenation_ofLetter, hD.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul, hzero _ u.2, hzero _ v.2, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, add_zero]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_zero]

/-! ### Taylor expansion of coderivations along coalgebra morphisms -/

/-- The length-`n` component of the Taylor expansion `gradedCoderivAlong G q F F' t`: either the
whole word is collapsed to the single letter `t(w)`, or a nonempty first block is collapsed by `t`
and prepended to `F'` of the rest, or a nonempty first block is twisted, collapsed by the Taylor
components of `F`, and prepended to the expansion of the rest. -/
private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if h : 0 < n then ofLetter R N ∘ₗ t ∘ₗ of R M ⟨n, h⟩ else 0) +
      (∑ d : Fin n, if h : 0 < d.1 then
        TensorProduct.lift ((prepend R N).compl₁₂ (t ∘ₗ of R M ⟨d.1, h⟩)
          (F' ∘ₗ of R M ⟨n - d.1, by omega⟩)) ∘ₗ TensorPower.splitAt R M n d.1 d.2.le
        else 0) +
      (∑ d : Fin n, if h : 0 < d.1 then
        TensorProduct.lift ((prepend R N).compl₁₂
          ((letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ
            of R M ⟨d.1, h⟩)
          (gradedCoderivAlongComponent G q F F' t (n - d.1))) ∘ₗ
            TensorPower.splitAt R M n d.1 d.2.le
        else 0)
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The `q`-twisted coderivation along coalgebra morphisms `F` and `F'` with Taylor components `t`:
on a word it sums `F(τ B₁) ⋯ F(τ B_{i - 1}) · t(Bᵢ) · F'(B_{i + 1} ⋯ B_k)` over all cuts into
consecutive nonempty blocks with one distinguished block collapsed by `t`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    gradedCoderivAlongComponent G q F F' t n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' t (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (t (subword R x 0 n)) +
        (∑ d ∈ Finset.range n,
          prepend R N (t (subword R x 0 d)) (F' (subword R x d (n - d)))) +
        (∑ d ∈ Finset.range n,
          prepend R N
            (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x 0 d))))
            (gradedCoderivAlong G q F F' t (subword R x d (n - d)))) := by
  rw [gradedCoderivAlong, toModule_of, gradedCoderivAlongComponent, dite_eq_left hn,
    ← of_tprod_eq_subword R hn x]
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  · congr 1
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rcases Nat.eq_zero_or_pos d.1 with hd | hd
    · rw [dite_eq_right (by omega), hd, subword_length_zero, map_zero, map_zero,
        LinearMap.zero_apply, LinearMap.zero_apply]
    · have _ := d.isLt
      rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
        subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega)]
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
        TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
      congr 3
      exact of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rcases Nat.eq_zero_or_pos d.1 with hd | hd
    · rw [dite_eq_right (by omega), hd, subword_length_zero, map_zero, map_zero, map_zero,
        map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    · have _ := d.isLt
      rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
        subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega), toModule_of]
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
        TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
      congr 5
      exact of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' t (subword R x a b) =
      ofLetter R N (t (subword R x a b)) +
        (∑ d ∈ Finset.range b,
          prepend R N (t (subword R x a d)) (F' (subword R x (a + d) (b - d)))) +
        (∑ d ∈ Finset.range b,
          prepend R N
            (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d))))
            (gradedCoderivAlong G q F F' t (subword R x (a + d) (b - d)))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j _ ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' t) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' t hb, hy 0 b (by omega), Nat.add_zero]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
    · refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 h with hb | hab
      · have hb0 : b = 0 := by omega
        rw [hb0, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    have hs₁ : (∑ d ∈ Finset.range b,
        prepend R N (t (subword R x a d)) (F' (subword R x (a + d) (b - d)))) = 0 := by
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases not_and_or.1 h with hb | hab
      · omega
      · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero]
    have hs₂ : (∑ d ∈ Finset.range b,
        prepend R N
          (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d))))
          (gradedCoderivAlong G q F F' t (subword R x (a + d) (b - d)))) = 0 := by
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rcases not_and_or.1 h with hb | hab
      · omega
      · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero]
    rw [hs₁, hs₂, add_zero]

/-- The Taylor expansion `gradedCoderivAlong` has Taylor components `t`. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' t = t := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
    map_add, map_sum, map_sum, letter_ofLetter]
  simp only [letter_prepend, Finset.sum_const_zero, add_zero]

/-- On a single letter, `gradedCoderivAlong` is the single letter given by the arity-one
component. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (t : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' t (ofLetter R M a) = ofLetter R N (t (ofLetter R M a)) := by
  have h := gradedCoderivAlong_subword G q F F' t (fun _ : Fin 1 ↦ a) 0 1
  simp only [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    LinearMap.zero_apply, add_zero] at h
  exact h

/-- When `F` and `F'` are coalgebra morphisms, `gradedCoderivAlong G q F F' t` is a `q`-twisted
coderivation along `F` and `F'`. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong {q : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (t : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' t) := by
  set Fτ := F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) with hFτ_def
  set fτ := letter R N ∘ₗ Fτ with hfτ_def
  have hFτ : IsCoalgHom R Fτ := hF.comp (isCoalgHom_map _)
  have hFτ_eq : Fτ = coalgHom R fτ := hFτ.eq_coalgHom
  set D := gradedCoderivAlong G q F F' t with hD_def
  have hD_sub : ∀ {n : ℕ} (x : Fin n → M) (a b : ℕ),
      D (subword R x a b) =
        ofLetter R N (t (subword R x a b)) +
          (∑ d ∈ Finset.range b,
            prepend R N (t (subword R x a d)) (F' (subword R x (a + d) (b - d)))) +
          (∑ d ∈ Finset.range b,
            prepend R N (fτ (subword R x a d)) (D (subword R x (a + d) (b - d)))) := by
    intro n x a b
    simpa only [hD_def, hfτ_def, hFτ_def, LinearMap.comp_apply] using
      gradedCoderivAlong_subword G q F F' t x a b
  have hmap : TensorProduct.map F D ∘ₗ
      LinearMap.rTensor (ReducedTensorWords R M)
        (ReducedTensorWords.map (R := R) (G.koszulTwist q)) =
      TensorProduct.map Fτ D := by
    rw [LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id, hFτ_def]
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      deconcatenation R N (D (subword R x a b)) =
        TensorProduct.map D F' (deconcatenation R M (subword R x a b)) +
          TensorProduct.map Fτ D (deconcatenation R M (subword R x a b)) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      have hP₁ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N) (prepend R N (t (subword R x a d)))
              (deconcatenation R N (F' (subword R x (a + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              prepend R N (t (subword R x a d)) (F' (subword R x (a + d) c)) ⊗ₜ[R]
                F' (subword R x (a + d + c) (b - d - c)) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | _
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, Finset.sum_const_zero]
        · rw [hF'.deconcatenation_apply, map_deconcatenation_subword, map_sum]
          simp only [LinearMap.rTensor_tmul]
      have hP₂ : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N) (prepend R N (fτ (subword R x a d)))
              (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
            (∑ c ∈ Finset.range (b - d),
              prepend R N (fτ (subword R x a d)) (D (subword R x (a + d) c)) ⊗ₜ[R]
                F' (subword R x (a + d + c) (b - d - c))) +
            (∑ c ∈ Finset.range (b - d),
              prepend R N (fτ (subword R x a d)) (Fτ (subword R x (a + d) c)) ⊗ₜ[R]
                D (subword R x (a + d + c) (b - d - c))) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero]
        · rw [ih (b - d) (by omega), map_add, map_deconcatenation_subword,
            map_deconcatenation_subword, map_sum, map_sum]
          simp only [LinearMap.rTensor_tmul]
      have hdiag₁ : (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
            prepend R N (t (subword R x a d)) (F' (subword R x (a + d) c)) ⊗ₜ[R]
              F' (subword R x (a + d + c) (b - d - c))) =
          ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
            prepend R N (t (subword R x a d)) (F' (subword R x (a + d) (e - d))) ⊗ₜ[R]
              F' (subword R x (a + e) (b - e)) := by
        rw [← Finset.sum_range_diag_flip]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
          TensorProduct.zero_tmul, add_zero]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        rw [(by omega : a + d + (e - d) = a + e), (by omega : b - d - (e - d) = b - e)]
      have hdiag₂ : (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
            prepend R N (fτ (subword R x a d)) (D (subword R x (a + d) c)) ⊗ₜ[R]
              F' (subword R x (a + d + c) (b - d - c))) =
          ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
            prepend R N (fτ (subword R x a d)) (D (subword R x (a + d) (e - d))) ⊗ₜ[R]
              F' (subword R x (a + e) (b - e)) := by
        rw [← Finset.sum_range_diag_flip]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
          TensorProduct.zero_tmul, add_zero]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        rw [(by omega : a + d + (e - d) = a + e), (by omega : b - d - (e - d) = b - e)]
      have hdiag₃ : (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d),
            prepend R N (fτ (subword R x a d)) (Fτ (subword R x (a + d) c)) ⊗ₜ[R]
              D (subword R x (a + d + c) (b - d - c))) =
          ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e,
            prepend R N (fτ (subword R x a d)) (Fτ (subword R x (a + d) (e - d))) ⊗ₜ[R]
              D (subword R x (a + e) (b - e)) := by
        rw [← Finset.sum_range_diag_flip]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
          TensorProduct.zero_tmul, add_zero]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        rw [(by omega : a + d + (e - d) = a + e), (by omega : b - d - (e - d) = b - e)]
      have hFτ_sub : ∀ e : ℕ,
          Fτ (subword R x a e) =
            ofLetter R N (fτ (subword R x a e)) +
              ∑ d ∈ Finset.range e,
                prepend R N (fτ (subword R x a d)) (Fτ (subword R x (a + d) (e - d))) := by
        intro e
        conv_lhs => rw [hFτ_eq, coalgHom_subword]
        simp only [← hFτ_eq]
      rw [hD_sub, map_add, map_add, deconcatenation_ofLetter, zero_add, map_sum, map_sum,
        map_deconcatenation_subword, map_deconcatenation_subword]
      rw [Finset.sum_congr rfl fun d _ ↦ deconcatenation_prepend _ _,
        Finset.sum_congr rfl fun d _ ↦ deconcatenation_prepend _ _,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_congr rfl hP₁, Finset.sum_congr rfl hP₂, Finset.sum_add_distrib,
        hdiag₁, hdiag₂, hdiag₃]
      simp only [hD_sub x a, hFτ_sub, TensorProduct.add_tmul, TensorProduct.sum_tmul,
        Finset.sum_add_distrib]
      abel
  rw [isGradedCoderivationAlong_iff, ← LinearMap.comp_assoc, hmap]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- If `F` and `F'` have degree zero and `t` raises total degrees by `r`, then
`gradedCoderivAlong G q F F' t` raises total degrees by `r`. -/
theorem isHomogeneous_gradedCoderivAlong {q r : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {t : ReducedTensorWords R M →ₗ[R] N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF'₀ : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (ht : LinearMap.IsHomogeneous t (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' t) (gradedPiece G) (gradedPiece H) r := by
  have hτ₀ : LinearMap.IsHomogeneous (ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) (gradedPiece G) 0 :=
    isHomogeneous_map G G (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using G.koszulTwist_mem_piece hx q)
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' t w ∈ gradedPiece H (D + r)) hz ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have key : ∀ b a : ℕ, a + b ≤ n →
        gradedCoderivAlong G q F F' t (subword R x a b) ∈
          gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + r) := by
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        intro a hab
        rw [gradedCoderivAlong_subword]
        refine add_mem (add_mem ?_ (Submodule.sum_mem _ fun d hd ↦ ?_))
          (Submodule.sum_mem _ fun d hd ↦ ?_)
        · exact ofLetter_mem_gradedPiece H (ht.map_mem (subword_mem_gradedPiece x g hxg a b))
        · rw [Finset.mem_range] at hd
          rcases Nat.eq_zero_or_pos d with rfl | _
          · rw [subword_length_zero, map_zero, LinearMap.map_zero₂]
            exact zero_mem _
          · have hsum : (∑ j ∈ Finset.range b, g (a + j)) + r =
                ((∑ j ∈ Finset.range d, g (a + j)) + r) +
                  ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
              rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
              simp only [Nat.add_assoc]
              abel
            rw [hsum]
            refine prepend_mem_gradedPiece
              (ht.map_mem (subword_mem_gradedPiece x g hxg a d)) ?_
            simpa only [add_zero] using
              hF'₀.map_mem (subword_mem_gradedPiece x g hxg (a + d) (b - d))
        · rw [Finset.mem_range] at hd
          rcases Nat.eq_zero_or_pos d with rfl | hd0
          · rw [subword_length_zero, map_zero, map_zero, map_zero, LinearMap.map_zero₂]
            exact zero_mem _
          · have hsum : (∑ j ∈ Finset.range b, g (a + j)) + r =
                (∑ j ∈ Finset.range d, g (a + j)) +
                  ((∑ j ∈ Finset.range (b - d), g (a + d + j)) + r) := by
              rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
              simp only [Nat.add_assoc]
              abel
            rw [hsum]
            refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
            have h₁ := hτ₀.map_mem (subword_mem_gradedPiece x g hxg a d)
            rw [add_zero] at h₁
            have h₂ := hF₀.map_mem h₁
            rw [add_zero] at h₂
            simpa only [add_zero] using (isHomogeneous_letter H).map_mem h₂
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

/-- When `F'` preserves the conilpotence filtration, `gradedCoderivAlong G q F F' t` preserves
the conilpotence filtration. -/
theorem gradedCoderivAlong_mem_filtration {q : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : IsCoalgHom R F') (t : ReducedTensorWords R M →ₗ[R] N) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F F' t z ∈ filtration R N n := by
  have hsub : ∀ {l : ℕ} (x : Fin l → M) (b a : ℕ),
      gradedCoderivAlong G q F F' t (subword R x a b) ∈ filtration R N b := by
    intro l x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [subword_length_zero, map_zero]
        exact Submodule.zero_mem _
      rw [gradedCoderivAlong_subword]
      refine Submodule.add_mem _ (Submodule.add_mem _
        (filtration_monotone R N hb (ofLetter_mem_filtration R N _))
        (Submodule.sum_mem _ fun d hd ↦ ?_))
        (Submodule.sum_mem _ fun d hd ↦ ?_)
      · rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
          exact Submodule.zero_mem _
        · exact filtration_monotone R N (by omega) (prepend_mem_filtration R N _
            (hF'.mem_filtration (subword_mem_filtration R M x (a + d) le_rfl)))
      · rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
          exact Submodule.zero_mem _
        · exact filtration_monotone R N (by omega)
            (prepend_mem_filtration R N _ (ih (b - d) (by omega) (a + d)))
  have h : filtration R M n ≤ (filtration R N n).comap (gradedCoderivAlong G q F F' t) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _ (filtration_monotone R N hk (hsub y k.1 0))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact h hz

/-! ### Limits of stabilising Taylor maps -/

/-- The limit of a sequence of linear maps out of reduced tensor words: on words of length `k`, it
acts as the `k`-th map of the sequence.  When the sequence stabilises along the conilpotence
filtration, `stabilisingLimit t` agrees with `t n` on `filtration R M n` for every `n`. -/
noncomputable def stabilisingLimit (t : ℕ → ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun k ↦ t k.1 ∘ₗ of R M k

/-- In a sequence stabilising along the conilpotence filtration, `t n` agrees with `t k` on the
words of length at most `k`, for `k ≤ n`. -/
private theorem stabilising_apply_eq_of_le {t : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (ht : ∀ n, ∀ z ∈ filtration R M n, t (n + 1) z = t n z) {k n : ℕ} (hkn : k ≤ n)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) : t n z = t k z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [ht n z (filtration_monotone R M hkn hz), ih]

/-- On the words of length at most `n`, the limit of a stabilising sequence agrees with `t n`. -/
theorem stabilisingLimit_apply_of_mem_filtration {t : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (ht : ∀ n, ∀ z ∈ filtration R M n, t (n + 1) z = t n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    stabilisingLimit t z = t n z := by
  have h : filtration R M n ≤ LinearMap.eqLocus (stabilisingLimit t) (t n) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, stabilisingLimit, toModule_of, LinearMap.comp_apply,
      stabilising_apply_eq_of_le ht hk (of_mem_filtration R M le_rfl x)]
  exact h hz

/-- If every map in a stabilising sequence is homogeneous of degree `r`, so is its limit. -/
theorem isHomogeneous_stabilisingLimit {t : ℕ → ReducedTensorWords R M →ₗ[R] N} {r : ℤ}
    (ht : ∀ n, ∀ z ∈ filtration R M n, t (n + 1) z = t n z)
    (hhom : ∀ n, LinearMap.IsHomogeneous (t n) (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (stabilisingLimit t) (gradedPiece G) H.piece r := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [stabilisingLimit_apply_of_mem_filtration ht hn]
  exact (hhom n).map_mem hz

/-- The coalgebra morphism of `stabilisingLimit t` agrees with that of `t n` on the words of
length at most `n`. -/
theorem coalgHom_stabilisingLimit_apply_of_mem_filtration {t : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (ht : ∀ n, ∀ z ∈ filtration R M n, t (n + 1) z = t n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    coalgHom R (stabilisingLimit t) z = coalgHom R (t n) z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun w hw ↦ by
      rw [← LinearMap.comp_apply (letter R N), letter_comp_coalgHom,
        ← LinearMap.comp_apply (letter R N), letter_comp_coalgHom,
        stabilisingLimit_apply_of_mem_filtration ht hw]) hz

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

/-- The negation of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.neg {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q F F' (-D) := by
  have heq : (-1 : R) • D = -D := LinearMap.ext fun z ↦ neg_one_smul R (D z)
  rw [← heq]
  exact hD.smul (-1)

/-- The difference of two coderivations along the same pair of maps is a coderivation along
them. -/
theorem IsGradedCoderivationAlong.sub {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') := by
  have heq : D + -D' = D - D' := LinearMap.ext fun z ↦ (sub_eq_add_neg (D z) (D' z)).symm
  rw [← heq]
  exact hD.add hD'.neg

/-- When two `q`-twisted coderivations `D₁` (along `F₁, F₁'`) and `D₂` (along `F₂, F₂'`) agree on
the words of length at most `n`, and `F₁ = F₂`, `F₁' = F₂'` on those words, their difference takes
primitive values on the words of length at most `n + 1`: every cut of such a word has both halves
of length at most `n`, so the two deconcatenations cancel. -/
theorem IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ u ∈ filtration R M n, F₁ u = F₂ u)
    (hF' : ∀ v ∈ filtration R M n, F₁' v = F₂' v)
    (hD : ∀ w ∈ filtration R M n, D₁ w = D₂ w)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D₁ z - D₂ z = ofLetter R N (letter R N (D₁ z) - letter R N (D₂ z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (by rw [map_sub, letter_ofLetter])
  rw [deconcatenation_ofLetter, map_sub, h₁.deconcatenation_apply, h₂.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hτu : map (R := R) (G.koszulTwist q) u ∈ filtration R M n :=
        (isCoalgHom_map _).mem_filtration u.2
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, hD _ u.2, hD _ v.2, hF' _ v.2, hF _ hτu, sub_self]
  | add u v ihu ihv =>
      simp only [map_add] at ihu ihv ⊢
      convert congrArg₂ (· + ·) ihu ihv using 1 <;> abel

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

/-- On a word of length at most `n + 1`, the graded commutator `b_N ∘ D - (-1)^(q r) D ∘ b_M`
satisfies the `(t + q)`-twisted co-Leibniz identity along `F` and `F'` as soon as `F` and `F'`
intertwine `b_M` and `b_N` on the words of length at most `n`: every cut of such a word has both
halves of length at most `n`. -/
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
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ u ∈ filtration R M n, bN (F u) = F (bM u))
    (hF' : ∀ v ∈ filtration R M n, bN (F' v) = F' (bM v))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) z) =
      TensorProduct.map (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) F'
          (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM))
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist (t + q))) (deconcatenation R M z)) := by
  set c : R := (((q * r).negOnePow : ℤ) : R) with hc
  -- The commutation rules of the maps involved with the letterwise twists.
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
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [map_sub, map_smul, hbN.deconcatenation_apply, hD.deconcatenation_apply,
    hD.deconcatenation_apply, hbM.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  -- On each cut `u ⊗ v`, both halves have length at most `n`, and the cross terms
  -- `b_N F τ_t u ⊗ D v` and `τ_q D u ⊗ b_N F' v` cancel against those of `(-1)^(q r) Δ (D ∘ b_M)`.
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hFb : bN (F (ReducedTensorWords.map (R := R) (G.koszulTwist t) u)) =
          F (bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) u)) :=
        hF _ ((isCoalgHom_map _).mem_filtration u.2)
      have hF'b : bN (F' v) = F' (bM v) := hF' _ v.2
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, map_smul,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hτF, hτD, hτb, hττ, hττ',
        hFb, hF'b, TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', smul_add, hcc]
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
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using
    hD.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration hD₁ hbM hbM₁ hs hbN hF₀
      (fun u _ ↦ LinearMap.congr_fun hF u) (fun v _ ↦ LinearMap.congr_fun hF' v)
      (filtration_monotone R M n.le_succ hn)

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

/-- When `F` and `F'` are coalgebra morphisms intertwining odd coderivations `b_M` and `b_N` on the
words of length at most `n`, and the homotopy defect `(F - F') - (b_N ∘ D + D ∘ b_M)` vanishes on
those words, that defect takes primitive values on the words of length at most `n + 1`: its
deconcatenation on such a word splits into cuts whose halves have length at most `n`. -/
theorem IsGradedCoderivationAlong.sub_sub_comp_add_comp_eq_ofLetter_of_mem_filtration {q r s : ℤ}
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
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {n : ℕ}
    (hF : ∀ u ∈ filtration R M n, bN (F u) = F (bM u))
    (hF' : ∀ v ∈ filtration R M n, bN (F' v) = F' (bM v))
    (hzero : ∀ w ∈ filtration R M n, ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) w = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    ((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z =
      ofLetter R N (letter R N (((F - F') - (bN ∘ₗ D + D ∘ₗ bM)) z)) := by
  set R_def := (F - F') - (bN ∘ₗ D + D ∘ₗ bM) with hR_def
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [deconcatenation_ofLetter]
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun w ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, sub_neg_eq_add]
  have hτ : G.koszulTwist (q + q) = LinearMap.id := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self]
  have hdec₁ := (hFc.isGradedCoderivationAlong_sub (G := G) hF'c).deconcatenation_apply z
  rw [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id] at hdec₁
  have hdec₂ := hD.deconcatenation_comp_sub_negOnePow_smul_comp_of_mem_filtration hD₁ hbM hbM₁
    (hs.trans hr.symm) hbN hF₀ hF hF' hz
  rw [he, hτ, ReducedTensorWords.map_id, LinearMap.rTensor_id] at hdec₂
  rw [hR_def, LinearMap.sub_apply, map_sub, hdec₁, hdec₂]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hu : (F - F') u = (bN ∘ₗ D + D ∘ₗ bM) u := sub_eq_zero.1 (hzero _ u.2)
      have hv : (F - F') v = (bN ∘ₗ D + D ∘ₗ bM) v := sub_eq_zero.1 (hzero _ v.2)
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, TensorProduct.map_tmul,
        LinearMap.id_apply, hu, hv, sub_self]
  | add u v ihu ihv =>
      simp only [map_add] at ihu ihv ⊢
      convert congrArg₂ (· + ·) ihu ihv using 1 <;> abel

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
