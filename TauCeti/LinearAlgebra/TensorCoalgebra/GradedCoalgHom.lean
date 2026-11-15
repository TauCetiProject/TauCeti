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
  a pair of coalgebra morphisms with prescribed letter component.

## Main results

* `TauCeti.ReducedTensorWords.isHomogeneous_coalgHom`: the Taylor expansion of degree-zero
  components has degree zero.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.eq_of_letter_comp_eq` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration_of_apply_eq`:
  a coderivation along a pair of maps is determined by its letter component, and on short words
  by its letter component and the endpoint maps on shorter words.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong`, and
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: `gradedCoderivAlong` is a
  coderivation along coalgebra morphisms with the prescribed letter component and degree.
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

/-- Two coderivations along pairs of maps that agree on shorter words and have the same letter
components on the words of length at most `n` agree on those words: the deconcatenation of a word
of length at most `n` only involves words of length at most `n - 1`. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration_of_apply_eq {q : ℤ}
    {F₁ F'₁ D₁ F₂ F'₂ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F'₁ D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F'₂ D₂) {n : ℕ}
    (hF : ∀ u ∈ filtration R M (n - 1), F₁ u = F₂ u)
    (hF' : ∀ u ∈ filtration R M (n - 1), F'₁ u = F'₂ u)
    (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      simp only [(Submodule.mem_bot R).1 hz, map_zero]
  | succ n ih =>
      have ih' : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun w hw ↦ hF w (filtration_monotone R M (by omega) hw))
          (fun w hw ↦ hF' w (filtration_monotone R M (by omega) hw))
          (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
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
    {n : ℕ} (hl : ∀ w ∈ filtration R M n, letter R N (D₁ w) = letter R N (D₂ w))
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
    (hl : ∀ w ∈ filtration R M n, letter R N (D w) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D z = 0 :=
  hD.apply_eq_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
    (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- A coderivation along a pair of maps that vanishes on the words of length at most `n` sends
every word of length at most `n + 1` to the single letter given by its letter component: every
cut of such a word has both halves of length at most `n`. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (h₀ : ∀ u ∈ filtration R M n, D u = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [deconcatenation_ofLetter, hD.deconcatenation_apply, ← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul]
      rw [h₀ _ u.2, h₀ _ v.2, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_zero]

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

/-! ### Taylor expansion of coderivations along coalgebra morphisms -/

/-- The length-`n` component of `gradedCoderivAlong G q F F' h`: either the whole word is
collapsed to the single letter `h(x₁ ⋯ xₙ)`, or a nonempty prefix of `d` letters is separated,
producing `h(prefix) · F'(rest)` and `π(F(τ(prefix))) · D(rest)`. -/
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
            (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
              of R M ⟨d.1, hd⟩)
            (gradedCoderivAlongComponent G q F F' h (n - d.1)))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The Taylor expansion of a `q`-twisted coderivation along coalgebra morphisms `F` and `F'`
with letter component `h`: on a word `z`, summing over cuts into blocks with one distinguished
block mapped by `h`, blocks to its left mapped by the Taylor components of `F ∘ τ_q`, and the
suffix to its right mapped by `F'`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ gradedCoderivAlongComponent G q F F' h n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' h (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (h (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          (prepend R N (h (subword R x 0 d)) (F' (subword R x d (n - d))) +
            prepend R N
              (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x 0 d))))
              (gradedCoderivAlong G q F F' h (subword R x d (n - d)))) := by
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
    have hpre : of R M ⟨d.1, hd⟩
        (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x (Fin.castLE d.2.le i)) =
        subword R x 0 d.1 := by
      rw [subword_eq_of_tprod R x hd (by omega)]
      exact of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [dite_eq_left hd, subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega),
      toModule_of]
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
      LinearMap.add_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, hpre]

/-- The recursive evaluation rule of `gradedCoderivAlong` on a subword. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) =
      ofLetter R N (h (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
            prepend R N
              (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
                (subword R x a d))))
              (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d)))) := by
  by_cases hb_ab : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := hb_ab
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j _ ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' h) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' h hb, hy 0 b (by omega), Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 hb_ab with hb | hab
      · rw [show b = 0 from by omega, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 hb_ab with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero, map_zero,
        map_zero, add_zero]

/-- The letter component of `gradedCoderivAlong G q F F' h` is `h`. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' h = h := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add,
    map_sum, letter_ofLetter]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong G q F F' h` is the single letter given by `h`. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' h (ofLetter R M a) = ofLetter R N (h (ofLetter R M a)) := by
  have heq := gradedCoderivAlong_subword G q F F' h (fun _ : Fin 1 ↦ a) 0 1
  rw [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero] at heq
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using heq

/-- Reindex a triangular sum over consecutive subword cuts `(d, c)` by `e = d + c`, dropping the
empty middle block `c = 0`. -/
private theorem sum_range_subword_flip {V : Type*} [AddCommMonoid V] {b a : ℕ}
    (g : ℕ → ℕ → ℕ → ℕ → V) (h0 : ∀ e, g e 0 (a + e) (b - e) = 0) :
    (∑ d ∈ Finset.range b, ∑ c ∈ Finset.range (b - d), g d c (a + d + c) (b - d - c)) =
      ∑ e ∈ Finset.range b, ∑ d ∈ Finset.range e, g d (e - d) (a + e) (b - e) := by
  rw [← Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [Finset.mem_range] at he
  rw [Finset.sum_range_succ, Nat.sub_self, show a + e + 0 = a + e from by omega,
    show b - e - 0 = b - e from by omega, h0 e, add_zero]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.mem_range] at hd
  rw [show a + d + (e - d) = a + e from by omega, show b - d - (e - d) = b - e from by omega]

/-- Recursive expansion of `F ∘ map (koszulTwist q)` on a subword when `F` is a coalgebra
morphism. -/
private theorem apply_map_koszulTwist_subword {q : ℤ}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    {n : ℕ} (x : Fin n → M) (c e : ℕ) :
    F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x c e)) =
      ofLetter R N (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
        (subword R x c e)))) +
        ∑ d ∈ Finset.range e,
          prepend R N (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x c d))))
            (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
              (subword R x (c + d) (e - d)))) := by
  have hFeq := (hF.comp (isCoalgHom_map (G.koszulTwist q))).eq_coalgHom
  have key := congrFun (congrArg DFunLike.coe hFeq) (subword R x c e)
  rw [coalgHom_subword] at key
  simpa only [← hFeq, LinearMap.comp_apply] using key

/-- Block induction for the co-Leibniz rule of `gradedCoderivAlong` along coalgebra morphisms. -/
private theorem deconcatenation_gradedCoderivAlong_subword {q : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N)
    {n : ℕ} (x : Fin n → M) (b a : ℕ) :
    deconcatenation R N (gradedCoderivAlong G q F F' h (subword R x a b)) =
      (TensorProduct.map (gradedCoderivAlong G q F F' h) F' +
        TensorProduct.map F (gradedCoderivAlong G q F F' h) ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)))
        (deconcatenation R M (subword R x a b)) := by
  set D := gradedCoderivAlong G q F F' h
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have hrT : TensorProduct.map F D ∘ₗ LinearMap.rTensor (ReducedTensorWords R M) τ =
      TensorProduct.map (F ∘ₗ τ) D := by
    rw [LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id]
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    have hP₂ : ∀ d ∈ Finset.range b,
        LinearMap.rTensor (ReducedTensorWords R N)
            (prepend R N (letter R N (F (τ (subword R x a d)))))
            (deconcatenation R N (D (subword R x (a + d) (b - d)))) =
          ∑ c ∈ Finset.range (b - d),
            (prepend R N (letter R N (F (τ (subword R x a d))))
                (D (subword R x (a + d) c)) ⊗ₜ[R] F' (subword R x (a + d + c) (b - d - c)) +
              prepend R N (letter R N (F (τ (subword R x a d))))
                (F (τ (subword R x (a + d) c))) ⊗ₜ[R]
                D (subword R x (a + d + c) (b - d - c))) := by
      rintro (_ | d) hd
      · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
          TensorProduct.zero_tmul, add_zero, Finset.sum_const_zero]
      · rw [Finset.mem_range] at hd
        rw [ih (b - (d + 1)) (by omega) (a + (d + 1)), hrT, LinearMap.add_apply,
          map_deconcatenation_subword, map_deconcatenation_subword, map_add, map_sum, map_sum,
          ← Finset.sum_add_distrib]
        simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]
    rw [gradedCoderivAlong_subword G q F F' h x a b, map_add, deconcatenation_ofLetter, zero_add,
      map_sum, hrT, LinearMap.add_apply, map_deconcatenation_subword, map_deconcatenation_subword]
    simp only [map_add, deconcatenation_prepend, hF'.deconcatenation_apply,
      map_deconcatenation_subword, map_sum, LinearMap.rTensor_tmul, Finset.sum_add_distrib,
      LinearMap.comp_apply]
    rw [Finset.sum_congr rfl hP₂, sum_range_subword_flip
        (fun d c p s ↦ prepend R N (h (subword R x a d)) (F' (subword R x (a + d) c)) ⊗ₜ[R]
          F' (subword R x p s))
        (fun _ ↦ by simp only [subword_length_zero, map_zero, TensorProduct.zero_tmul]),
      sum_range_subword_flip
        (fun d c p s ↦
          prepend R N (letter R N (F (τ (subword R x a d)))) (D (subword R x (a + d) c)) ⊗ₜ[R]
            F' (subword R x p s) +
          prepend R N (letter R N (F (τ (subword R x a d))))
            (F (τ (subword R x (a + d) c))) ⊗ₜ[R] D (subword R x p s))
        (fun _ ↦ by simp only [subword_length_zero, map_zero, TensorProduct.zero_tmul, add_zero])]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    conv_rhs => rw [show D (subword R x a e) = _ from gradedCoderivAlong_subword G q F F' h x a e,
      show F (τ (subword R x a e)) = _ from apply_map_koszulTwist_subword hF x a e]
    simp only [D, τ, TensorProduct.add_tmul, TensorProduct.sum_tmul, Finset.sum_add_distrib]
    abel

/-- When `F` and `F'` are coalgebra morphisms, `gradedCoderivAlong G q F F' h` is a `q`-twisted
coderivation along `F` and `F'`. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' h) := by
  rw [isGradedCoderivationAlong_iff]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2,
    deconcatenation_gradedCoderivAlong_subword hF hF' h x n.1 0]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]

/-- Every `q`-twisted coderivation along coalgebra morphisms `F` and `F'` is the Taylor expansion
of its own letter component. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Block induction for the homogeneity of `gradedCoderivAlong`. -/
private theorem gradedCoderivAlong_subword_mem_gradedPiece {q p : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF'₀ : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    {h : ReducedTensorWords R M →ₗ[R] N}
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) H.piece p)
    {n : ℕ} (x : Fin n → M) (g : ℕ → ℤ) (hxg : ∀ i : Fin n, x i ∈ G.piece (g i))
    (b a : ℕ) (hab : a + b ≤ n) :
    gradedCoderivAlong G q F F' h (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + p) := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [gradedCoderivAlong_subword]
    refine add_mem
      (ofLetter_mem_gradedPiece H (hh.map_mem (subword_mem_gradedPiece x g hxg a b)))
      (Submodule.sum_mem _ fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, zero_mem]
    · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
          (∑ j ∈ Finset.range d, g (a + j)) + ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
        rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
        simp only [Nat.add_assoc]
      set S₁ := ∑ j ∈ Finset.range d, g (a + j)
      set S₂ := ∑ j ∈ Finset.range (b - d), g (a + d + j)
      have hsub₁ := subword_mem_gradedPiece x g hxg a d
      have hsub₂ := subword_mem_gradedPiece x g hxg (a + d) (b - d)
      have hτ₁ : ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d) ∈
          gradedPiece G S₁ := by
        rw [map_koszulTwist_apply_of_mem G hsub₁ q]
        exact Submodule.smul_mem _ _ hsub₁
      have hfτ₁ : letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q)
          (subword R x a d))) ∈ H.piece S₁ := by
        simpa only [add_zero] using (isHomogeneous_letter H).map_mem (hF₀.map_mem hτ₁)
      have hF'₂ : F' (subword R x (a + d) (b - d)) ∈ gradedPiece H S₂ := by
        simpa only [add_zero] using hF'₀.map_mem hsub₂
      rw [hsum]
      refine add_mem ?_ ?_
      · rw [show S₁ + S₂ + p = (S₁ + p) + S₂ from by abel]
        exact prepend_mem_gradedPiece (hh.map_mem hsub₁) hF'₂
      · rw [show S₁ + S₂ + p = S₁ + (S₂ + p) from by abel]
        exact prepend_mem_gradedPiece hfτ₁ (ih (b - d) (by omega) (a + d) (by omega))

/-- When `F` and `F'` have degree zero and `h` has degree `p`, `gradedCoderivAlong G q F F' h`
is homogeneous of degree `p`. -/
theorem isHomogeneous_gradedCoderivAlong {q p : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF'₀ : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    {h : ReducedTensorWords R M →ₗ[R] N}
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) H.piece p) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' h) (gradedPiece G) (gradedPiece H) p := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' h w ∈ gradedPiece H (D + p)) hz ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if hk : k < n then 𝒟 ⟨k, hk⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
      rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact gradedCoderivAlong_subword_mem_gradedPiece hF₀ hF'₀ hh x g hxg n 0 (by omega)
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- `gradedCoderivAlong` does not increase tensor length on a subword when `F'` preserves the
conilpotence filtration. -/
private theorem gradedCoderivAlong_subword_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ ⦃k : ℕ⦄ ⦃z : ReducedTensorWords R M⦄, z ∈ filtration R M k → F' z ∈ filtration R N k)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) ∈ filtration R N b := by
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
    · refine Submodule.add_mem _ ?_ ?_
      · exact filtration_monotone R N (by omega)
          (prepend_mem_filtration R N _ (hF' (subword_mem_filtration R M x (a + d) le_rfl)))
      · exact filtration_monotone R N (by omega)
          (prepend_mem_filtration R N _ (ih (b - d) (by omega) (a + d)))

/-- `gradedCoderivAlong` preserves the conilpotence filtration when `F'` does. -/
theorem gradedCoderivAlong_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ ⦃k : ℕ⦄ ⦃z : ReducedTensorWords R M⦄, z ∈ filtration R M k → F' z ∈ filtration R N k)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) :
    gradedCoderivAlong G q F F' h z ∈ filtration R N n := by
  have hle : filtration R M n ≤ (filtration R N n).comap (gradedCoderivAlong G q F F' h) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _
          (filtration_monotone R N hk
            (gradedCoderivAlong_subword_mem_filtration G q F hF' h y 0 k.1))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact hle hz

/-- Every coderivation along coalgebra morphisms preserves the conilpotence filtration. -/
theorem IsGradedCoderivationAlong.mem_filtration {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    {n : ℕ} {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    D z ∈ filtration R N n := by
  rw [hD.eq_gradedCoderivAlong hF hF']
  exact gradedCoderivAlong_mem_filtration G q F (fun _ _ hw ↦ hF'.mem_filtration hw) _ hz

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
  set c : R := (((q * r).negOnePow : ℤ) : R) with hc
  -- The commutation rules of the maps involved with the letterwise twists.
  have hτF : ∀ z, ReducedTensorWords.map (R := R) (H.koszulTwist q) (F z) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) z) := fun z ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) z
  have hτD : ∀ z, ReducedTensorWords.map (R := R) (H.koszulTwist q) (D z) =
      c • D (ReducedTensorWords.map (R := R) (G.koszulTwist q) z) := fun z ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) z
  have hτb : ∀ z, ReducedTensorWords.map (R := R) (G.koszulTwist t) (bM z) =
      c • bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) z) := fun z ↦ by
    simpa only [hs, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp t) z
  have hττ : ∀ z, ReducedTensorWords.map (R := R) (G.koszulTwist q)
      (ReducedTensorWords.map (R := R) (G.koszulTwist t) z) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) z := fun z ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp, add_comm]
  have hττ' : ∀ z, ReducedTensorWords.map (R := R) (G.koszulTwist t)
      (ReducedTensorWords.map (R := R) (G.koszulTwist q) z) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) z := fun z ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp, InternalGrading.koszulTwist_comp]
  have hcc : ∀ x : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N, c • c • x = x := by
    intro x
    rw [smul_smul, hc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_smul]
  have hFb : ∀ z, bN (F z) = F (bM z) := LinearMap.congr_fun hF
  have hF'b : ∀ z, bN (F' z) = F' (bM z) := LinearMap.congr_fun hF'
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  rw [map_sub, map_smul, hbN.deconcatenation_apply, hD.deconcatenation_apply,
    hD.deconcatenation_apply, hbM.deconcatenation_apply]
  -- On each cut `u ⊗ v`, the cross terms `b_N F τ_t u ⊗ D v` and `τ_q D u ⊗ b_N F' v` of
  -- `Δ (b_N ∘ D)` cancel against those of `(-1)^(q r) Δ (D ∘ b_M)`, leaving the co-Leibniz terms
  -- of the commutator.
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [map_add, map_smul, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, hτF, hτD, hτb, hττ, hττ', hFb, hF'b, TensorProduct.tmul_sub,
        TensorProduct.sub_tmul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_add,
        hcc]
      abel
  | add u v hu hv =>
      simp only [map_add, smul_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

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
