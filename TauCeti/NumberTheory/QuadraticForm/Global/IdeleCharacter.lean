/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The Hilbert character of the idele group

For `b ∈ Kˣ` in a number field `K`, the **idele Hilbert character** of `b` is the homomorphism

`φ_b : 𝕀_K →* {±1},   φ_b(x) = ∏_v (x_v, b)_v,`

where `v` runs over all places of `K`, `x_v` is the coordinate of the idele `x` at `v`, and
`(·, ·)_v` is the norm-equation Hilbert symbol `TauCeti.hilbertSymbol` read over the completion
`K_v`. The product is a finite one: at a finite place not above `2` at which both `x_v` and `b` are
local units the symbol is `1`, and almost every finite place is of this kind. It is multiplicative
because the Hilbert symbol is multiplicative in its first argument over every nonarchimedean local
field, and over `ℝ` and `ℂ`.

By the norm-equation definition of the symbol, `(x_v, b)_v = 1` says that `x_v` is a norm from
`K_v(√b)`, so an idele lies in the kernel of `φ_b` exactly when it is a local non-norm at an even
number of places. This is the character used in the proof of Hilbert sign prescription
(O'Meara 71:19a) to describe the subgroup `Kˣ · N_{K(√b)/K}(𝕀_{K(√b)})` of `𝕀_K` as the kernel of
`φ_b`. That description also needs the product formula for the Hilbert symbol, the fact that the
coordinates of an idele norm are local norms, and the norm index theorem, none of which is proved
here.

This file constructs `φ_b`, computes it on the ideles concentrated at one place, and proves that it
is onto `{±1}` exactly when `b` is a nonsquare at some finite or real place, in which case its
kernel has index two. A complex place contributes nothing, since every element of `ℂ` is a square.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter`: the idele Hilbert character `φ_b`.

## Main results

* `TauCeti.NumberField.QuadraticForm.hasFiniteMulSupport_hilbertSymbol_ideleFiniteCoord`: the
  local symbols `(x_v, b)_v` at the finite places have finite support.
* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_apply`: the product formula defining
  `φ_b`.
* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_ofAdicCompletion`,
  `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_ofCompletion`: on an idele
  concentrated at one place, `φ_b` is the local symbol at that place.
* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_ofCompletion_of_isReal`: at a real
  place that local symbol is the real symbol, read through the real embedding.
* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_eq_one_iff`: `φ_b` is trivial exactly
  when `b` is a square at every finite place and positive at every real place.
* `TauCeti.NumberField.QuadraticForm.ideleHilbertCharacter_surjective_iff`,
  `TauCeti.NumberField.QuadraticForm.index_ker_ideleHilbertCharacter`: otherwise `φ_b` is onto
  `{±1}`, and its kernel has index two.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19 and 71:19a.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §2.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-! ### The local symbols -/

/-- **Finite support of the local symbols of an idele.** For an idele `x` and `b ∈ Kˣ`, the
Hilbert symbol `(x_v, b)_v` over the completion `K_v` is `1` at all but finitely many finite
places `v`. -/
theorem hasFiniteMulSupport_hilbertSymbol_ideleFiniteCoord (x : IdeleGroup (𝓞 K) K) (b : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      hilbertSymbol (v.ideleFiniteCoord x) (v.unitAtFinitePlace b) := by
  -- Almost every finite coordinate of an idele is a local unit.
  have hx : IsUnit (x : AdeleRing (𝓞 K) K).2 :=
    x.isUnit.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  refine hasFiniteMulSupport_hilbertSymbol_of_eventually_valued_eq_one ?_ b
  filter_upwards [(FiniteAdeleRing.isUnit_iff.mp hx).2] with v hv
  rwa [coe_ideleFiniteCoord]

/-! ### The character -/

/-- **The idele Hilbert character** `φ_b(x) = ∏_v (x_v, b)_v` of `b ∈ Kˣ`: the product over all
places `v` of `K` of the Hilbert symbol, over the completion `K_v`, of the coordinate `x_v` of the
idele `x` and the image of `b`. The product over the finite places is a finite one by
`hasFiniteMulSupport_hilbertSymbol_ideleFiniteCoord`. -/
def ideleHilbertCharacter (b : Kˣ) : IdeleGroup (𝓞 K) K →* ℤˣ where
  toFun x := (∏ w : InfinitePlace K, hilbertSymbol (w.ideleInfiniteCoord x)
      (Units.map (algebraMap K w.Completion).toMonoidHom b)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), hilbertSymbol (v.ideleFiniteCoord x) (v.unitAtFinitePlace b)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, hilbertSymbol_completion_mul_left, hilbertSymbol_mul_left_adicCompletion,
      Finset.prod_mul_distrib]
    rw [finprod_mul_distrib (hasFiniteMulSupport_hilbertSymbol_ideleFiniteCoord x b)
      (hasFiniteMulSupport_hilbertSymbol_ideleFiniteCoord y b), mul_mul_mul_comm]

/-- The idele Hilbert character is the product of the local Hilbert symbols at the infinite and
at the finite places. -/
theorem ideleHilbertCharacter_apply (b : Kˣ) (x : IdeleGroup (𝓞 K) K) :
    ideleHilbertCharacter b x = (∏ w : InfinitePlace K, hilbertSymbol (w.ideleInfiniteCoord x)
      (Units.map (algebraMap K w.Completion).toMonoidHom b)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), hilbertSymbol (v.ideleFiniteCoord x) (v.unitAtFinitePlace b) :=
  (rfl)

/-- On an idele concentrated at a finite place `v`, the idele Hilbert character of `b` is the
Hilbert symbol over `K_v` of the coordinate at `v` and the image of `b`. -/
@[simp]
theorem ideleHilbertCharacter_ofAdicCompletion (b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleHilbertCharacter b (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) =
      hilbertSymbol u (v.unitAtFinitePlace b) := by
  rw [ideleHilbertCharacter_apply, finprod_eq_single _ v fun v' hv' ↦ by
      rw [ideleFiniteCoord_ofAdicCompletion_of_ne v' hv', hilbertSymbol_one_left]]
  simp

/-- On an idele concentrated at an infinite place `w`, the idele Hilbert character of `b` is the
Hilbert symbol over the completion `K_w` of the coordinate at `w` and the image of `b`. -/
@[simp]
theorem ideleHilbertCharacter_ofCompletion (b : Kˣ) (w : InfinitePlace K) (u : w.Completionˣ) :
    ideleHilbertCharacter b (IdeleGroup.ofCompletion (𝓞 K) K w u) =
      hilbertSymbol u (Units.map (algebraMap K w.Completion).toMonoidHom b) := by
  rw [ideleHilbertCharacter_apply, Finset.prod_eq_single w (fun w' _ hw' ↦ by
      rw [ideleInfiniteCoord_ofCompletion_of_ne w' hw', hilbertSymbol_completion_one_left])
      (by simp)]
  simp

/-- On an idele concentrated at a real place `w`, the idele Hilbert character of `b` is the real
Hilbert symbol of the coordinate at `w`, read in `ℝ`, and the image of `b` under the real
embedding at `w`. -/
theorem ideleHilbertCharacter_ofCompletion_of_isReal (b : Kˣ)
    (w : {w : InfinitePlace K // w.IsReal}) (u : w.1.Completionˣ) :
    ideleHilbertCharacter b (IdeleGroup.ofCompletion (𝓞 K) K w.1 u) =
      hilbertSymbol (Units.map (Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →* ℝ) u)
        (unitAtRealPlace w b) := by
  rw [ideleHilbertCharacter_ofCompletion, ← units_map_ringEquivRealOfIsReal_algebraMap,
    hilbertSymbol_units_map_ringEquiv]

/-! ### Triviality and surjectivity -/

/-- **Triviality of the idele Hilbert character.** `φ_b` is trivial exactly when `b` is a square
in the completion at every finite place and positive at every real place. -/
theorem ideleHilbertCharacter_eq_one_iff (b : Kˣ) :
    ideleHilbertCharacter b = 1 ↔
      (∀ v : HeightOneSpectrum (𝓞 K), IsSquare (v.unitAtFinitePlace b)) ∧
        ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < embedding_of_isReal w.2 (b : K) := by
  constructor
  · intro h
    refine ⟨fun v ↦ ?_, fun w ↦ ?_⟩
    · -- A nonsquare at `v` has a local non-norm partner, concentrated at `v` it is an idele.
      by_contra hb
      let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      obtain ⟨u, hu⟩ := exists_hilbertSymbol_eq_neg_one two_ne_zero hb
      have h1 := DFunLike.congr_fun h (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)
      rw [ideleHilbertCharacter_ofAdicCompletion, MonoidHom.one_apply,
        hilbertSymbol_comm, hu] at h1
      exact absurd h1 (by decide)
    · -- An element negative at `w` has symbol `-1` with `-1` there.
      have h1 := DFunLike.congr_fun h (IdeleGroup.ofCompletion (𝓞 K) K w.1 (-1))
      have hneg : Units.map (Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →* ℝ) (-1) =
          -1 :=
        Units.ext (by simp)
      rw [ideleHilbertCharacter_ofCompletion_of_isReal, MonoidHom.one_apply, hneg,
        hilbertSymbol_real_eq_one_iff, unitAtRealPlace_apply] at h1
      exact h1.resolve_left (by norm_num)
  · rintro ⟨hfin, hreal⟩
    refine MonoidHom.ext fun x ↦ ?_
    rw [ideleHilbertCharacter_apply, MonoidHom.one_apply,
      finprod_eq_one_of_forall_eq_one fun v ↦ hilbertSymbol_eq_one_of_isSquare_right _ (hfin v),
      mul_one]
    refine Finset.prod_eq_one fun w _ ↦ ?_
    rcases w.isReal_or_isComplex with hw | hw
    · rw [← hilbertSymbol_units_map_ringEquiv (Completion.ringEquivRealOfIsReal hw),
        units_map_ringEquivRealOfIsReal_algebraMap ⟨w, hw⟩]
      exact hilbertSymbol_eq_one_of_isSquare_right _
        ((isSquare_unitAtRealPlace_iff ⟨w, hw⟩ b).mpr (hreal ⟨w, hw⟩))
    · exact hilbertSymbol_completion_eq_one_of_isComplex hw _ _

/-- **Surjectivity of the idele Hilbert character.** `φ_b` is onto `{±1}` exactly when `b` is a
nonsquare in the completion at some finite place or negative at some real place. -/
theorem ideleHilbertCharacter_surjective_iff (b : Kˣ) :
    Function.Surjective (ideleHilbertCharacter b) ↔
      (∃ v : HeightOneSpectrum (𝓞 K), ¬IsSquare (v.unitAtFinitePlace b)) ∨
        ∃ w : {w : InfinitePlace K // w.IsReal}, embedding_of_isReal w.2 (b : K) < 0 := by
  -- A homomorphism to the two-element group `ℤˣ` is onto exactly when it is nontrivial.
  have hsurj : Function.Surjective (ideleHilbertCharacter b) ↔ ideleHilbertCharacter b ≠ 1 := by
    have : Fact (Nat.card ℤˣ).Prime :=
      ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]; exact Nat.prime_two⟩
    rw [← MonoidHom.range_eq_top, Ne, ← MonoidHom.range_eq_bot_iff]
    have : Nontrivial ℤˣ := ⟨⟨1, -1, by decide⟩⟩
    rcases (ideleHilbertCharacter b).range.eq_bot_or_eq_top_of_prime_card with h | h <;> simp [h]
  rw [hsurj, Ne, ideleHilbertCharacter_eq_one_iff, not_and_or, not_forall, not_forall]
  refine or_congr Iff.rfl (exists_congr fun w ↦ ?_)
  rw [← isSquare_unitAtRealPlace_iff, not_isSquare_unitAtRealPlace_iff]

/-- **The kernel of the idele Hilbert character has index two** when `b` is a nonsquare in the
completion at some finite place or negative at some real place. -/
theorem index_ker_ideleHilbertCharacter {b : Kˣ}
    (hb : (∃ v : HeightOneSpectrum (𝓞 K), ¬IsSquare (v.unitAtFinitePlace b)) ∨
      ∃ w : {w : InfinitePlace K // w.IsReal}, embedding_of_isReal w.2 (b : K) < 0) :
    (ideleHilbertCharacter b).ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    ((ideleHilbertCharacter_surjective_iff b).mpr hb), Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

end TauCeti.NumberField.QuadraticForm
