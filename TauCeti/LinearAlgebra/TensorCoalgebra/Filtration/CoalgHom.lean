/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coderivation
import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Coalgebra morphisms of reduced tensor coalgebras close to the identity

Let `φ : Tᶜ(M) ⟶ M` vanish on the words of length at most `e`.  The coalgebra morphism
`F = coalgHom (letter + φ)`, whose Taylor components are those of the identity perturbed by `φ`,
sends a word to the sum, over all ways of cutting it into consecutive blocks, of the word in which
some blocks are collapsed by `φ`.  A collapsed block has more than `e` letters, so `F` is the
identity on the words of length at most `e`, and on a word of length at most `2 e + 1` at most one
block is collapsed, so `F` agrees there with `id + coderiv φ`, the identity plus the coderivation
collapsing one block by `φ`.  On a word of length at most `3 e + 2` at most two blocks are
collapsed, and `2 (F - id - coderiv φ) = D ∘ D - coderiv (φ ∘ D)` there, for `D = coderiv φ`:
the square `D ∘ D` collapses two disjoint blocks once in each order, and its nested collapses form
the coderivation of `φ ∘ D`.

This is the length bound behind gauge transformations of `A∞` structures: such a transformation
changes the Taylor map on short words only through one insertion of `φ`.  The second-order bound
computes the quadratic term of an `A∞` morphism whose linear part is the identity.

## Main results

* `TauCeti.ReducedTensorWords.coalgHom_letter_add_apply_eq_self_of_mem_filtration`: the coalgebra
  morphism with Taylor components `letter + φ` is the identity on the words of length at most `e`.
* `TauCeti.ReducedTensorWords.coalgHom_letter_add_apply_of_mem_filtration`: the coalgebra
  morphism with Taylor components `letter + φ` is `id + coderiv φ` on the words of length at most
  `2 e + 1`.
* `TauCeti.ReducedTensorWords.two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration`: the
  coalgebra morphism with Taylor components `letter + φ` satisfies
  `2 (F - id - D) = D ∘ D - coderiv (φ ∘ D)` on the words of length at most `3 e + 2`.
* `TauCeti.ReducedTensorWords.lengthProj_two_coalgHom_of_tprod`: the length-two component of
  `coalgHom f` on a pure tensor word is the sum over all cuts into two nonempty blocks.
* `TauCeti.ReducedTensorWords.lengthProj_two_coalgHom_letter_add_sub_coderiv_of_tprod`: when `φ`
  vanishes on letters and `n ≥ 1`, the length-two component of
  `coalgHom (letter + φ) - coderiv φ` on a pure word `x` of length `n + 2` is the sum over
  `2 ≤ d ≤ n` of the two-letter words `φ(x₀ ⋯ x_{d-1}) ⊗ φ(x_d ⋯ x_{n+1})`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, for gauge transformations of `A∞` structures.
-/

public section

open scoped TensorProduct

universe uR uM

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism of the reduced tensor coalgebra vanishes on the words of length at most `n`
when, for every `k < n`, vanishing on the words of length at most `k` forces its values on the
words of length at most `k + 1` to have zero letter and zero deconcatenation. -/
private theorem apply_eq_zero_of_mem_filtration_of_succ
    {Y : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (n : ℕ)
    (hstep : ∀ k < n, (∀ z ∈ filtration R M k, Y z = 0) → ∀ z ∈ filtration R M (k + 1),
      letter R M (Y z) = 0 ∧ deconcatenation R M (Y z) = 0) :
    ∀ z ∈ filtration R M n, Y z = 0 := by
  induction n with
  | zero =>
      intro z hz
      rw [filtration_zero, Submodule.mem_bot] at hz
      rw [hz, map_zero]
  | succ k ih =>
      intro z hz
      obtain ⟨hl, hd⟩ := hstep k (Nat.lt_succ_self k) (ih fun i hi ↦ hstep i (by omega)) z hz
      exact eq_of_deconcatenation_eq_of_letter_eq R M (by rw [hd, map_zero])
        (by rw [hl, map_zero])

/-- The letter of the value of the coalgebra morphism with Taylor components `letter + φ`. -/
private theorem letter_coalgHom_letter_add_apply (φ : ReducedTensorWords R M →ₗ[R] M)
    (z : ReducedTensorWords R M) :
    letter R M (coalgHom R (letter R M + φ) z) = letter R M z + φ z := by
  rw [← LinearMap.comp_apply (letter R M), letter_comp_coalgHom, LinearMap.add_apply]

/-- The coalgebra morphism with Taylor components `letter + φ` is the identity on the words of
length at most `e`, when `φ` vanishes on them: there its Taylor components are those of the
identity. -/
theorem coalgHom_letter_add_apply_eq_self_of_mem_filtration
    {φ : ReducedTensorWords R M →ₗ[R] M} {e : ℕ} (hφ : ∀ z ∈ filtration R M e, φ z = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M e) :
    coalgHom R (letter R M + φ) z = z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_id M)
    (fun w hw ↦ by rw [letter_coalgHom_letter_add_apply, hφ w hw, add_zero, LinearMap.id_apply])
    hz

/- The proof below does not expand `coalgHom`.  It shows by induction along the conilpotence
filtration that `F - id - coderiv φ` vanishes on the words of length at most `2 e + 1`, where
`F = coalgHom (letter + φ)`.  The letter component of `F - id - coderiv φ` is zero, and the
co-Leibniz rules of `F` and `coderiv φ` express the deconcatenation of a value through values on
shorter words.  This leaves the term `(F - id) ⊗ (F - id)`, which vanishes since every cut of a
word of length at most `2 e + 1` has a half of length at most `e`, on which `F - id` vanishes. -/

/-- **A coalgebra morphism close to the identity.**  If `φ` vanishes on the words of length at most
`e`, then the coalgebra morphism with Taylor components `letter + φ` is `id + coderiv φ` on the
words of length at most `2 e + 1`: collapsing two blocks by `φ` needs at least `2 (e + 1)`
letters. -/
theorem coalgHom_letter_add_apply_of_mem_filtration {φ : ReducedTensorWords R M →ₗ[R] M} {e : ℕ}
    (hφ : ∀ z ∈ filtration R M e, φ z = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (2 * e + 1)) :
    coalgHom R (letter R M + φ) z = z + coderiv R φ z := by
  have hF : IsCoalgHom R (coalgHom R (letter R M + φ)) := isCoalgHom_coalgHom _
  have hD : IsCoderivation R (coderiv R φ) := isCoderivation_coderiv R φ
  have hX : ∀ z ∈ filtration R M e,
      (coalgHom R (letter R M + φ) - LinearMap.id : Module.End R (ReducedTensorWords R M)) z =
        0 := fun z hz ↦ by
    rw [LinearMap.sub_apply, LinearMap.id_apply,
      coalgHom_letter_add_apply_eq_self_of_mem_filtration hφ hz, sub_self]
  suffices h : ∀ z ∈ filtration R M (2 * e + 1),
      (coalgHom R (letter R M + φ) - LinearMap.id - coderiv R φ :
        Module.End R (ReducedTensorWords R M)) z = 0 by
    have hz' := h z hz
    rwa [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, sub_sub,
      sub_eq_zero] at hz'
  refine apply_eq_zero_of_mem_filtration_of_succ (2 * e + 1) fun k hk ih z hz ↦ ⟨?_, ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_sub,
      letter_coalgHom_letter_add_apply, LinearMap.id_apply, ← LinearMap.comp_apply (letter R M),
      letter_comp_coderiv, add_sub_cancel_left, sub_self]
  · -- The terms `(F - id - D) ⊗ id` and `id ⊗ (F - id - D)` vanish on the cuts of `z` by
    -- induction, and `(F - id) ⊗ (F - id)` since every cut of a word of length at most `2 e + 1`
    -- has a half of length at most `e`.
    generalize coalgHom R (letter R M + φ) = F at hF hX ih ⊢
    have h := TensorProduct.map_sub_sub_add_eq F (coderiv R φ) (deconcatenation R M z)
    rw [map_deconcatenation_eq_zero_of_mem_filtration R M ih
        (apply_eq_zero_of_mem_filtration_zero R M _) (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M
        (apply_eq_zero_of_mem_filtration_zero R M _) ih
        (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M hX hX
        (filtration_monotone R M (by omega) hz), add_zero, add_zero,
      ← hF.deconcatenation_apply, ← hD.deconcatenation_apply] at h
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_sub, LinearMap.id_apply, h]

/-- On cuts, the defect `2 (F - id - D) - (D ∘ D - D')` of the coalgebra morphism `F` from its
second-order expansion, for coderivations `D` and `D'`, deconcatenates to the defect on either
half plus twice the terms in which both halves move. -/
private theorem two_smul_map_sub_eq (F D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (w : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    (2 : R) • (TensorProduct.map F F w - w -
        (LinearMap.rTensor _ D w + LinearMap.lTensor _ D w)) -
      (LinearMap.rTensor _ D (LinearMap.rTensor _ D w + LinearMap.lTensor _ D w) +
          LinearMap.lTensor _ D (LinearMap.rTensor _ D w + LinearMap.lTensor _ D w) -
        (LinearMap.rTensor _ D' w + LinearMap.lTensor _ D' w)) =
      LinearMap.rTensor _ ((2 : R) • (F - LinearMap.id - D) - (D ∘ₗ D - D')) w +
        LinearMap.lTensor _ ((2 : R) • (F - LinearMap.id - D) - (D ∘ₗ D - D')) w +
        (2 : R) • (TensorProduct.map D (F - LinearMap.id - D) w +
          TensorProduct.map (F - LinearMap.id - D) D w +
          TensorProduct.map (F - LinearMap.id - D) (F - LinearMap.id - D) w) := by
  -- Cache the additive group instance of pairs of words, which `linear_combination` otherwise
  -- fails to synthesize.
  let : AddCommGroup (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) := inferInstance
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_add, TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul,
      ← TensorProduct.smul_tmul']
    module
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    linear_combination (norm := module) hx + hy

/- The proof below follows that of `coalgHom_letter_add_apply_of_mem_filtration` one order further.
Writing `F = id + D + Y`, the defect `X = 2 Y - (D ∘ D - D')` has zero letter component, and its
deconcatenation is `X ⊗ id + id ⊗ X` plus twice `D ⊗ Y + Y ⊗ D + Y ⊗ Y`.  These last terms vanish
on the words of length at most `3 e + 2`, since `D` vanishes on the words of length at most `e` and
`Y` on those of length at most `2 e + 1`. -/

/-- **A coalgebra morphism close to the identity, to second order.**  If `φ` vanishes on the words
of length at most `e`, then on the words of length at most `3 e + 2` the coalgebra morphism `F`
with Taylor components `letter + φ` satisfies `2 (F - id - D) = D ∘ D - coderiv (φ ∘ D)`, where
`D = coderiv φ`: there at most two blocks are collapsed by `φ`, and `D ∘ D` collapses two
disjoint blocks once in each order, while its nested collapses form `coderiv (φ ∘ D)`. -/
theorem two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration
    {φ : ReducedTensorWords R M →ₗ[R] M} {e : ℕ} (hφ : ∀ z ∈ filtration R M e, φ z = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (3 * e + 2)) :
    (2 : R) • (coalgHom R (letter R M + φ) z - z - coderiv R φ z) =
      coderiv R φ (coderiv R φ z) - coderiv R (φ ∘ₗ coderiv R φ) z := by
  have hF : IsCoalgHom R (coalgHom R (letter R M + φ)) := isCoalgHom_coalgHom _
  have hD : IsCoderivation R (coderiv R φ) := isCoderivation_coderiv R φ
  have hD' : IsCoderivation R (coderiv R (φ ∘ₗ coderiv R φ)) := isCoderivation_coderiv R _
  have hY : ∀ z ∈ filtration R M (2 * e + 1),
      (coalgHom R (letter R M + φ) - LinearMap.id - coderiv R φ :
        Module.End R (ReducedTensorWords R M)) z = 0 := fun z hz ↦ by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      coalgHom_letter_add_apply_of_mem_filtration hφ hz, add_sub_cancel_left, sub_self]
  have hDe : ∀ z ∈ filtration R M e, coderiv R φ z = 0 := fun z hz ↦ by
    have h := coalgHom_letter_add_apply_of_mem_filtration hφ
      (filtration_monotone R M (by omega) hz)
    rwa [coalgHom_letter_add_apply_eq_self_of_mem_filtration hφ hz, left_eq_add] at h
  suffices h : ∀ z ∈ filtration R M (3 * e + 2),
      ((2 : R) • (coalgHom R (letter R M + φ) - LinearMap.id - coderiv R φ) -
        (coderiv R φ ∘ₗ coderiv R φ - coderiv R (φ ∘ₗ coderiv R φ)) :
          Module.End R (ReducedTensorWords R M)) z = 0 by
    have hz' := h z hz
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply] at hz'
    rwa [sub_eq_zero] at hz'
  refine apply_eq_zero_of_mem_filtration_of_succ (3 * e + 2) fun k hk ih z hz ↦ ⟨?_, ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_smul, letter_coalgHom_letter_add_apply]
    rw [← LinearMap.comp_apply (letter R M) (coderiv R φ), letter_comp_coderiv,
      ← LinearMap.comp_apply (letter R M) (coderiv R φ), letter_comp_coderiv,
      ← LinearMap.comp_apply (letter R M) (coderiv R _), letter_comp_coderiv,
      LinearMap.comp_apply]
    simp
  · -- The defect deconcatenates to the defect on either half, which vanishes by induction, plus
    -- terms moving both halves, which vanish on short words.
    generalize coalgHom R (letter R M + φ) = F at hF hY ih ⊢
    generalize coderiv R φ = D at hD hD' hY hDe ih ⊢
    generalize coderiv R (φ ∘ₗ D) = D' at hD' ih ⊢
    have h := two_smul_map_sub_eq F D D' (deconcatenation R M z)
    rw [← hF.deconcatenation_apply, ← hD.deconcatenation_apply, ← hD.deconcatenation_apply,
      ← hD'.deconcatenation_apply] at h
    simp only [LinearMap.rTensor_def, LinearMap.lTensor_def] at h
    rw [map_deconcatenation_eq_zero_of_mem_filtration R M ih
        (apply_eq_zero_of_mem_filtration_zero R M _) (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M
        (apply_eq_zero_of_mem_filtration_zero R M _) ih (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M hDe hY
        (filtration_monotone R M (by omega) hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M hY hDe
        (filtration_monotone R M (by omega) hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M hY hY
        (filtration_monotone R M (by omega) hz)] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_smul]
    simpa using h

/-! ### The length-two component of a coalgebra morphism -/

/-- The `ℕ+` numeral `2` and the positive-length subtype element `⟨2, two_pos⟩` name the same
length-two inclusion, stated at fixed tensor power so `rw` needs no dependent motive. -/
private theorem of_pnat_two_eq {N : Type*} [AddCommMonoid N] [Module R N]
    (z : TensorPower R 2 N) :
    of R N (2 : ℕ+) z = of R N ⟨2, two_pos⟩ z :=
  rfl

/-- The length-two component of a prepended word `a · w` pairs `a` with the letter of `w`:
every component of `w` of length at least two gives a prepended word of length at least three. -/
private theorem lengthProj_two_prepend {N : Type*} [AddCommMonoid N] [Module R N]
    (a : N) (w : ReducedTensorWords R N) :
    lengthProj R N ⟨2, two_pos⟩ (prepend R N a w) =
      of R N ⟨2, two_pos⟩ (PiTensorProduct.tprod R ![a, letter R N w]) := by
  have key : lengthProj R N ⟨2, two_pos⟩ ∘ₗ prepend R N a =
      prepend R N a ∘ₗ ofLetter R N ∘ₗ letter R N := by
    refine linearMap_ext R N fun ⟨k, hk0⟩ y ↦ ?_
    simp only [LinearMap.comp_apply]
    rcases eq_or_ne k 1 with rfl | hk
    · rw [of_tprod_eq_subword R hk0, subword_one R N y hk0, letter_ofLetter,
        prepend_ofLetter, of_pnat_two_eq, lengthProj_of_self]
    · have hk1 : (⟨k, hk0⟩ : {n : ℕ // 0 < n}) ≠ 1 := by
        simp only [ne_eq, Subtype.ext_iff, Positive.val_one]
        exact hk
      have hk2 : (⟨k + 1, Nat.succ_pos _⟩ : {n : ℕ // 0 < n}) ≠ ⟨2, two_pos⟩ := by
        simp only [ne_eq, Subtype.mk.injEq]
        omega
      rw [prepend_of_tprod, lengthProj_of_of_ne R N hk2, letter_of_of_ne_one R N hk1, map_zero,
        map_zero]
  have hw := LinearMap.congr_fun key w
  simp only [LinearMap.comp_apply] at hw
  rw [hw, prepend_ofLetter, of_pnat_two_eq]

/-- **The length-two component of `coalgHom f` on a pure tensor word**: it is the sum, over all
cuts of the word into two nonempty blocks, of the two-letter word formed by applying `f` to each
block. -/
theorem lengthProj_two_coalgHom_of_tprod {N : Type*} [AddCommMonoid N] [Module R N]
    (f : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    lengthProj R N ⟨2, two_pos⟩ (coalgHom R f (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x))) =
      ∑ d ∈ Finset.Ioo 0 n, of R N ⟨2, two_pos⟩
        (PiTensorProduct.tprod R ![f (subword R x 0 d), f (subword R x d (n - d))]) := by
  rw [of_tprod_eq_subword R hn, coalgHom_subword, map_add, map_sum, ofLetter_eq_of_tprod,
    lengthProj_of_of_ne R N (by decide), zero_add]
  have h0 : of R N ⟨2, two_pos⟩ (PiTensorProduct.tprod R
      ![f (subword R x 0 0), f (subword R x 0 (n - 0))]) = 0 := by
    rw [subword_length_zero, map_zero,
      (PiTensorProduct.tprod R).map_coord_zero (m := ![0, _]) 0 rfl, map_zero]
  rw [sum_Ioo_eq_sum_range _ _ h0]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [lengthProj_two_prepend, ← LinearMap.comp_apply (letter R N), letter_comp_coalgHom,
    Nat.zero_add]

/-- The length-two component of `coderiv φ` on a pure word of length `n + 2` (`n ≥ 1`): only the
two collapses of `n + 1` consecutive letters leave a two-letter word. -/
private theorem lengthProj_two_coderiv_of_tprod (φ : ReducedTensorWords R M →ₗ[R] M)
    {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 2) → M) :
    lengthProj R M ⟨2, two_pos⟩
        (coderiv R φ (of R M ⟨n + 2, by omega⟩ (PiTensorProduct.tprod R x))) =
      of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R ![φ (subword R x 0 (n + 1)),
        x (Fin.last (n + 1))]) +
      of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R ![x 0, φ (subword R x 1 (n + 1))]) := by
  rw [of_tprod_eq_subword R (by omega), coderiv_subword R φ x (K := n + 2) le_rfl, map_sum]
  have hinner (p : ℕ) : lengthProj R M ⟨2, two_pos⟩
      (∑ d ∈ Finset.range (n + 2 + 1), splice R x 0 (n + 2) p d
        (φ (subword R x (0 + p) d))) =
      lengthProj R M ⟨2, two_pos⟩ (splice R x 0 (n + 2) p (n + 1) (φ (subword R x p (n + 1)))) := by
    rw [map_sum]
    refine (Finset.sum_eq_single (n + 1) (fun d _ hd ↦ ?_) (by simp)).trans ?_
    · by_cases hfit : 0 < d ∧ p + d ≤ n + 2
      · rw [splice_eq_of_tprod R x _ hfit.1 hfit.2 (by omega),
          lengthProj_of_of_ne R M (by simp only [ne_eq, Subtype.mk.injEq]; omega)]
      · rw [splice_eq_zero_of_not_fits R x _ hfit, map_zero]
    · rw [Nat.zero_add]
  rw [Finset.sum_congr rfl fun p _ ↦ hinner p, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_eq_zero fun p _ ↦ by
      rw [splice_eq_zero_of_block_lt_add R x _ (by omega), map_zero],
    zero_add, splice_collapse_tail_eq R (n := n + 1) (by omega),
    splice_collapse_init_eq R (n := n + 1) (by omega), of_pnat_two_eq, of_pnat_two_eq,
    lengthProj_of_self, lengthProj_of_self, Nat.zero_add, add_comm]

/-- **The length-two component of `coalgHom (letter + φ) - coderiv φ` on a pure word.**  When `φ`
vanishes on single letters and `n ≥ 1`, subtracting `coderiv φ` cancels the two cuts with a
single-letter block, leaving the cuts of `x` into two blocks each of length at least two. -/
theorem lengthProj_two_coalgHom_letter_add_sub_coderiv_of_tprod
    {φ : ReducedTensorWords R M →ₗ[R] M} (hφ : ∀ z ∈ filtration R M 1, φ z = 0)
    {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 2) → M) :
    lengthProj R M ⟨2, two_pos⟩ (coalgHom R (letter R M + φ)
        (of R M ⟨n + 2, by omega⟩ (PiTensorProduct.tprod R x)) -
      coderiv R φ (of R M ⟨n + 2, by omega⟩ (PiTensorProduct.tprod R x))) =
      ∑ d ∈ Finset.Icc 2 n, of R M ⟨2, two_pos⟩
        (PiTensorProduct.tprod R ![φ (subword R x 0 d), φ (subword R x d (n + 2 - d))]) := by
  have hIoo : ((Finset.Ioo 0 (n + 2)).erase 1).erase (n + 1) = Finset.Icc 2 n := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [map_sub, lengthProj_two_coalgHom_of_tprod _ (by omega), lengthProj_two_coderiv_of_tprod φ hn,
    ← Finset.add_sum_erase _ _ (Finset.mem_Ioo.2 ⟨by omega, by omega⟩ : 1 ∈ _),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨by omega, Finset.mem_Ioo.2 ⟨by omega, by omega⟩⟩
      : n + 1 ∈ _),
    hIoo]
  have hd1 : of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R
      ![(letter R M + φ) (subword R x 0 1), (letter R M + φ) (subword R x 1 (n + 2 - 1))]) =
      of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R ![x 0, φ (subword R x 1 (n + 1))]) := by
    have hsub : n + 2 - 1 = n + 1 := by omega
    rw [hsub, subword_one R M x (by omega), LinearMap.add_apply, letter_ofLetter,
      hφ _ (ofLetter_mem_filtration R M _), add_zero, LinearMap.add_apply,
      letter_subword_of_ne_one R M x 1 (by omega), zero_add, Fin.zero_eta]
  have hdn : of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R
      ![(letter R M + φ) (subword R x 0 (n + 1)),
        (letter R M + φ) (subword R x (n + 1) (n + 2 - (n + 1)))]) =
      of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R
        ![φ (subword R x 0 (n + 1)), x (Fin.last (n + 1))]) := by
    have hsub : n + 2 - (n + 1) = 1 := by omega
    rw [hsub, subword_one R M x (by omega), LinearMap.add_apply,
      letter_subword_of_ne_one R M x 0 (by omega), zero_add, LinearMap.add_apply, letter_ofLetter,
      hφ _ (ofLetter_mem_filtration R M _), add_zero, ← Fin.last]
  have hmid : ∀ d ∈ Finset.Icc 2 n, of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R
      ![(letter R M + φ) (subword R x 0 d), (letter R M + φ) (subword R x d (n + 2 - d))]) =
      of R M ⟨2, two_pos⟩ (PiTensorProduct.tprod R
        ![φ (subword R x 0 d), φ (subword R x d (n + 2 - d))]) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [LinearMap.add_apply, letter_subword_of_ne_one R M x 0 (by omega), zero_add,
      LinearMap.add_apply, letter_subword_of_ne_one R M x d (by omega), zero_add]
  rw [hd1, hdn, Finset.sum_congr rfl hmid]
  abel

end TauCeti.ReducedTensorWords
