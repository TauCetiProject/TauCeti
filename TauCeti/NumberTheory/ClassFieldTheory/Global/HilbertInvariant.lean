/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalInvariant
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass
import TauCeti.NumberTheory.ClassFieldTheory.Local.TameSymbol
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# The cohomological Hilbert invariants at all places

Let `K` be a number field and `a, b ∈ Kˣ`. At a finite place `v` of `K`, the **Hilbert invariant**
`finiteHilbertInvariantAt K v a b ∈ ZMod 2` is the cohomological local symbol of the images of
`a` and `b` in the completion `K_v`: the cup product of their Kummer classes in `H¹(G_{K_v}, μ₂)`
along the pairing of the primitive square root of unity `-1`, followed by the normalized local
invariant `H²(G_{K_v}, μ₂) ≃+ ZMod 2`, which sends a class of Brauer invariant `1/2` to `1`. It is
the additive form of the quadratic Hilbert symbol `(a, b)_v`.

The finite invariant is bilinear and symmetric in `a` and `b`, and vanishes at every finite place
`v` not above `2` at which `a` and `b` are both units: there `K_v(√b)` is unramified, so every
unit is a norm from it. Only finitely many places are excluded, so the finite invariants of a fixed
pair have finite support, the finite set `finiteHilbertSupport K a b`. The sum of the invariants
over that set,
together with the archimedean invariants, is the left-hand side of Hilbert's reciprocity law.
The comparison `finiteInvAt_kummerBrauerClass` identifies every finite term with the localization
of the global Kummer-cup Brauer class, so this sum can be read in the global Brauer sequence.
At an infinite place, the corresponding invariant is defined by the same local cup product and
the archimedean invariant map; `infiniteInvAt_kummerBrauerClass` identifies it with the
localization of that same global class. At a real place it is `1` exactly when `a` and `b` are both
negative there, while at a complex place it is `0`; it is again bilinear and symmetric.

## Main definitions

* `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt K v a b`: the cohomological Hilbert
  invariant of `a` and `b` at the finite place `v`.
* `TauCeti.ClassFieldTheory.finiteHilbertSupport K a b`: the finite set of the finite places at
  which it is nonzero.
* `TauCeti.ClassFieldTheory.infiniteHilbertInvariantAt K w a b`: the cohomological Hilbert
  invariant at an infinite place, with values in `ZMod 2`.

## Main results

* `TauCeti.ClassFieldTheory.toRatAddCircle_finiteHilbertInvariantAt`: the invariant, read in
  `ℚ/ℤ`, is the Brauer invariant of the cup product of the two Kummer classes.
* `TauCeti.ClassFieldTheory.infiniteInvAt_kummerBrauerClass`: the infinite-place invariant of the
  global Kummer-cup Brauer class is the image of `infiniteHilbertInvariantAt` in `ℚ/ℤ`.
* `TauCeti.ClassFieldTheory.infiniteHilbertInvariantAt_eq_ite_of_isReal`: at a real place
  the invariant
  is `1` exactly when both arguments are negative.
* `TauCeti.ClassFieldTheory.infiniteHilbertInvariantAt_eq_zero_of_isComplex`: at a complex
  place the
  invariant is `0`.
* `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt_mul_left`,
  `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt_mul_right`,
  `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt_comm`: bilinearity and symmetry.
* `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt_eq_zero_of_valuation_eq_one`: the invariant
  vanishes at a place not above `2` at which `a` and `b` are units.
* `TauCeti.ClassFieldTheory.hasFiniteSupport_finiteHilbertInvariantAt`: it vanishes at all but
  finitely many finite places.
* `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt_eq_zero_of_notMem`: it vanishes outside
  `finiteHilbertSupport K a b`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §§2–3.
* J. Neukirch, *Algebraic Number Theory*, Springer (1999), Chapter V, §3 and Chapter VI, §8.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField InfinitePlace _root_.ValuativeRel

variable (K : Type) [Field K] [NumberField K]

/-- **The cohomological Hilbert invariant at a finite place** `v` of a number field `K`: the local
symbol of the images of `a, b ∈ Kˣ` in the completion `K_v`, that is, the cup product of their
Kummer classes along the pairing of the primitive square root of unity `-1`, followed by the
normalized local invariant `H²(G_{K_v}, μ₂) ≃+ ZMod 2`. -/
def finiteHilbertInvariantAt (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) : ZMod 2 :=
  -- `K_v` has characteristic zero, so `-1` is a primitive square root of unity
  let hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  localSymbol (kummerCupPairing (-1) hζ)
    (h2MuEquivZMod (v.adicCompletion K) hζ.neZero'.out.isUnit)
    (kummerClass _ hζ.neZero'.out.isUnit
      (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a))
    (kummerClass _ hζ.neZero'.out.isUnit
      (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) b))

/-- The Hilbert invariant at a finite place is the local symbol of the localized elements, for
any proofs that `-1` is a primitive square root of unity and that `2` is a unit in `K_v`. -/
theorem finiteHilbertInvariantAt_def (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2) (h2 : IsUnit (2 : v.adicCompletion K)) :
    finiteHilbertInvariantAt K v a b =
      localSymbol (kummerCupPairing (-1) hζ) (h2MuEquivZMod (v.adicCompletion K) h2)
        (kummerClass _ h2
          (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a))
        (kummerClass _ h2
          (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) b)) :=
  (rfl)

/-- **The normalization of the Hilbert invariant.** Read in `ℚ/ℤ` through `k ↦ k/2`, the Hilbert
invariant at a finite place is the Brauer invariant of the cup product of the Kummer classes of
the localized elements. -/
theorem toRatAddCircle_finiteHilbertInvariantAt (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2) (h2 : IsUnit (2 : v.adicCompletion K)) :
    ZMod.toRatAddCircle 2 (finiteHilbertInvariantAt K v a b) =
      invMap (v.adicCompletion K) (h2MuToBr 2 (v.adicCompletion K)
        ((kummerCupPairing (-1) hζ).cup 1 1
          (kummerClass _ h2
            (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a))
          (kummerClass _ h2
            (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) b)))) := by
  rw [finiteHilbertInvariantAt_def K v a b hζ h2, localSymbol_apply, toRatAddCircle_h2MuEquivZMod]

/-- The finite Hilbert invariant is the local invariant of one global Kummer-cup Brauer class.
This identifies the finite terms of Hilbert reciprocity with Brauer localization. -/
theorem finiteInvAt_kummerBrauerClass (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finiteInvAt K v (kummerBrauerClass (-1) (.neg_one 0 (by decide)) a b) =
      ZMod.toRatAddCircle 2 (finiteHilbertInvariantAt K v a b) := by
  have hζv : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  have h2v : IsUnit (2 : v.adicCompletion K) := hζv.neZero'.out.isUnit
  rw [finiteInvAt_apply, brBaseChange_kummerBrauerClass _ _]
  simpa only [map_neg, map_one, kummerBrauerClass_def] using
    (toRatAddCircle_finiteHilbertInvariantAt K v a b hζv h2v).symm

/-- **The cohomological Hilbert invariant at an infinite place** `w` of a number field `K`.
It is the `ZMod 2`-valued invariant of the localized global Kummer-cup Brauer class at a real
place, and zero at a complex place. -/
def infiniteHilbertInvariantAt (w : InfinitePlace K) (a b : Kˣ) : ZMod 2 :=
  by
    classical
    exact if hw : w.IsReal then
      realInvEquiv (brCongr (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (kummerBrauerClass (algebraMap K w.Completion (-1))
          ((.neg_one 0 (by decide) : IsPrimitiveRoot (-1 : K) 2).map_of_injective
            (algebraMap K w.Completion).injective)
          (Units.map (algebraMap K w.Completion : K →* w.Completion) a)
          (Units.map (algebraMap K w.Completion : K →* w.Completion) b)))
    else 0

/-- At a real place `w`, the infinite Hilbert invariant of `a` and `b` is the invariant, in
`Br ℝ ≃ ZMod 2`, of the Kummer-cup Brauer class of their images in `K_w`, carried to `ℝ` along the
isomorphism `K_w ≃ ℝ`. -/
theorem infiniteHilbertInvariantAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (a b : Kˣ) :
    infiniteHilbertInvariantAt K w a b =
      realInvEquiv (brCongr (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (kummerBrauerClass (algebraMap K w.Completion (-1))
          ((.neg_one 0 (by decide) : IsPrimitiveRoot (-1 : K) 2).map_of_injective
            (algebraMap K w.Completion).injective)
          (Units.map (algebraMap K w.Completion : K →* w.Completion) a)
          (Units.map (algebraMap K w.Completion : K →* w.Completion) b))) := by
  rw [infiniteHilbertInvariantAt, dite_eq_left hw]

/-- The infinite Hilbert invariant vanishes at a complex place. -/
theorem infiniteHilbertInvariantAt_eq_zero_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (a b : Kˣ) : infiniteHilbertInvariantAt K w a b = 0 := by
  rw [infiniteHilbertInvariantAt,
    dite_eq_right (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]

/-- **The infinite Hilbert invariant is the invariant of the global Kummer-cup Brauer class**:
localizing `kummerBrauerClass (-1) hζ a b` at `w` and applying `infiniteInvMap` gives the
`ℚ/ℤ`-image of `infiniteHilbertInvariantAt`. -/
theorem infiniteInvAt_kummerBrauerClass (w : InfinitePlace K) (a b : Kˣ) :
    infiniteInvAt K w (kummerBrauerClass (-1) (.neg_one 0 (by decide)) a b) =
      ZMod.toRatAddCircle 2 (infiniteHilbertInvariantAt K w a b) := by
  classical
  rw [infiniteInvAt_apply]
  rcases w.isReal_or_isComplex with hw | hw
  · rw [brBaseChange_kummerBrauerClass _ _]
    rw [infiniteInvMap_of_isReal w hw]
    rw [infiniteHilbertInvariantAt, dite_eq_left hw]
    rw [AddMonoidHom.comp_apply]
    let x := brCongr (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (kummerBrauerClass (algebraMap K w.Completion (-1))
        ((.neg_one 0 (by decide) : IsPrimitiveRoot (-1 : K) 2).map_of_injective
          (algebraMap K w.Completion).injective)
        (Units.map (algebraMap K w.Completion : K →* w.Completion) a)
        (Units.map (algebraMap K w.Completion : K →* w.Completion) b))
    -- `change` unfolds only the local `let x`; no rewrite lemma names this abbreviation.
    -- The invariant normalization uses `realInv_apply` below, not unfolding of `realInv`.
    change realInv x = ZMod.toRatAddCircle 2 (realInvEquiv x)
    by_cases hx : x = 0
    · simp [realInv_apply, hx]
    · rw [realInv_apply, ite_eq_right hx]
      have hne : realInvEquiv x ≠ 0 := by
        intro h
        exact hx (realInvEquiv.injective (h.trans (map_zero _).symm))
      have hv : realInvEquiv x = 1 := by
        have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
        exact (h _).resolve_left hne
      rw [hv]
      exact (ZMod.toRatAddCircle_natCast 2 1).symm
  · rw [infiniteInvMap_of_isComplex w hw]
    rw [infiniteHilbertInvariantAt,
      dite_eq_right (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
    simp

/-- **The normalization of the Hilbert invariant at an infinite place.** Read in `ℚ/ℤ` through
`k ↦ k/2`, the Hilbert invariant is the archimedean Brauer invariant of the cup product of the
localized Kummer classes. -/
theorem toRatAddCircle_infiniteHilbertInvariantAt (w : InfinitePlace K) (a b : Kˣ)
    (hζ : IsPrimitiveRoot (-1 : w.Completion) 2) (h2 : IsUnit (2 : w.Completion)) :
    ZMod.toRatAddCircle 2 (infiniteHilbertInvariantAt K w a b) =
      infiniteInvMap w (h2MuToBr 2 w.Completion
        ((kummerCupPairing (-1) hζ).cup 1 1
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) a))
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) b)))) := by
  rw [← infiniteInvAt_kummerBrauerClass K w a b, infiniteInvAt_apply,
    brBaseChange_kummerBrauerClass]
  simp only [map_neg, map_one, kummerBrauerClass_def]

open scoped Classical in
/-- The Hilbert invariant at an infinite place, expressed directly in terms of the cup product of
the localized Kummer classes: it is `0` when that cup product vanishes and `1` otherwise. -/
theorem infiniteHilbertInvariantAt_eq_ite (w : InfinitePlace K) (a b : Kˣ)
    (hζ : IsPrimitiveRoot (-1 : w.Completion) 2) (h2 : IsUnit (2 : w.Completion)) :
    infiniteHilbertInvariantAt K w a b =
      if (kummerCupPairing (-1) hζ).cup 1 1
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) a))
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) b)) = 0
        then 0 else 1 := by
  have hinj := h2MuToBr_injective 2 w.Completion h2
  apply ZMod.toRatAddCircle_injective 2
  rw [toRatAddCircle_infiniteHilbertInvariantAt K w a b hζ h2]
  by_cases hx : (kummerCupPairing (-1) hζ).cup 1 1
      (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) a))
      (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) b)) = 0
  · rw [ite_eq_left hx, hx]
    simp
  · rw [ite_eq_right hx]
    rcases w.isReal_or_isComplex with hw | hw
    · rw [infiniteInvMap_apply_of_isReal w hw]
      simpa [realInv_apply, map_eq_zero_iff _ hinj, hx] using
        (ZMod.toRatAddCircle_natCast 2 1).symm
    · have h : (kummerCupPairing (-1) hζ).cup 1 1
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) a))
          (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) b)) = 0 :=
        hinj ((brCompletion_eq_zero_of_isComplex w hw _).trans (map_zero _).symm)
      exact (hx h).elim

/-- The Hilbert invariant at an infinite place vanishes exactly when the cup product of the
localized Kummer classes does. -/
theorem infiniteHilbertInvariantAt_eq_zero_iff (w : InfinitePlace K) (a b : Kˣ)
    (hζ : IsPrimitiveRoot (-1 : w.Completion) 2) (h2 : IsUnit (2 : w.Completion)) :
    infiniteHilbertInvariantAt K w a b = 0 ↔
      (kummerCupPairing (-1) hζ).cup 1 1
        (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) a))
        (kummerClass _ h2 (Units.map (algebraMap K w.Completion : K →* w.Completion) b)) = 0 := by
  rw [infiniteHilbertInvariantAt_eq_ite K w a b hζ h2]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false one_ne_zero h

/-- **The Hilbert invariant at a real place** is `1` exactly when both `a` and `b` are negative
there. -/
@[simp]
theorem infiniteHilbertInvariantAt_eq_ite_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (a b : Kˣ) :
    infiniteHilbertInvariantAt K w a b =
      if embedding_of_isReal hw (a : K) < 0 ∧ embedding_of_isReal hw (b : K) < 0 then 1 else 0 := by
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  have hζ : IsPrimitiveRoot (-1 : w.Completion) 2 := .neg_one 0 (by decide)
  have key := (infiniteHilbertInvariantAt_eq_zero_iff K w a b hζ hζ.neZero'.out.isUnit).trans
    (cup_kummerClass_eq_zero_iff_of_ringEquiv_real _ _ (Completion.ringEquivRealOfIsReal hw) hζ
      hζ.neZero'.out.isUnit)
  have he (x : Kˣ) : Completion.ringEquivRealOfIsReal hw
      (Units.map (algebraMap K w.Completion : K →* w.Completion) x : w.Completion) =
      embedding_of_isReal hw (x : K) := by
    simp
  rw [he, he] at key
  have ha := (map_ne_zero (embedding_of_isReal hw)).2 a.ne_zero
  have hb := (map_ne_zero (embedding_of_isReal hw)).2 b.ne_zero
  split_ifs with h
  · exact (by decide : ∀ y : ZMod 2, y ≠ 0 → y = 1) _ (key.not.2 (by grind))
  · exact key.2 (by grind)

/-- The Hilbert invariant at an infinite place is symmetric. -/
theorem infiniteHilbertInvariantAt_comm (w : InfinitePlace K) (a b : Kˣ) :
    infiniteHilbertInvariantAt K w a b = infiniteHilbertInvariantAt K w b a := by
  rcases w.isReal_or_isComplex with hw | hw
  · simp only [infiniteHilbertInvariantAt_eq_ite_of_isReal K hw, and_comm]
  · simp [infiniteHilbertInvariantAt_eq_zero_of_isComplex K hw]

/-- The Hilbert invariant at an infinite place is additive in its first argument. -/
theorem infiniteHilbertInvariantAt_mul_left (w : InfinitePlace K) (a a' b : Kˣ) :
    infiniteHilbertInvariantAt K w (a * a') b =
      infiniteHilbertInvariantAt K w a b + infiniteHilbertInvariantAt K w a' b := by
  rcases w.isReal_or_isComplex with hw | hw
  · simp only [infiniteHilbertInvariantAt_of_isReal K hw, map_mul, kummerBrauerClass_mul_left,
      map_add]
  · simp [infiniteHilbertInvariantAt_eq_zero_of_isComplex K hw]

/-- The Hilbert invariant at an infinite place is additive in its second argument. -/
theorem infiniteHilbertInvariantAt_mul_right (w : InfinitePlace K) (a b b' : Kˣ) :
    infiniteHilbertInvariantAt K w a (b * b') =
      infiniteHilbertInvariantAt K w a b + infiniteHilbertInvariantAt K w a b' := by
  simp only [infiniteHilbertInvariantAt_comm K w a, infiniteHilbertInvariantAt_mul_left]

/-- The Hilbert invariant at a finite place is additive in its first argument. -/
theorem finiteHilbertInvariantAt_mul_left (v : HeightOneSpectrum (𝓞 K)) (a a' b : Kˣ) :
    finiteHilbertInvariantAt K v (a * a') b =
      finiteHilbertInvariantAt K v a b + finiteHilbertInvariantAt K v a' b := by
  have hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  simp only [finiteHilbertInvariantAt_def K v _ _ hζ hζ.neZero'.out.isUnit, map_mul]
  exact localSymbol_kummerClass_mul _ _ _ _ _ _

/-- The Hilbert invariant at a finite place is additive in its second argument. -/
theorem finiteHilbertInvariantAt_mul_right (v : HeightOneSpectrum (𝓞 K)) (a b b' : Kˣ) :
    finiteHilbertInvariantAt K v a (b * b') =
      finiteHilbertInvariantAt K v a b + finiteHilbertInvariantAt K v a b' := by
  have hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  simp only [finiteHilbertInvariantAt_def K v _ _ hζ hζ.neZero'.out.isUnit, map_mul]
  exact localSymbol_kummerClass_mul_right _ _ _ _ _ _

/-- The Hilbert invariant at a finite place is symmetric. -/
theorem finiteHilbertInvariantAt_comm (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finiteHilbertInvariantAt K v a b = finiteHilbertInvariantAt K v b a := by
  have hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  rw [finiteHilbertInvariantAt_def K v _ _ hζ hζ.neZero'.out.isUnit, localSymbol_antisymm,
    ZMod.neg_eq_self_mod_two, finiteHilbertInvariantAt_def K v _ _ hζ hζ.neZero'.out.isUnit]

/-- **The Hilbert invariant at a good finite place.** If `2`, `a` and `b` are units at the finite
place `v`, then the Hilbert invariant of `a` and `b` at `v` vanishes. -/
theorem finiteHilbertInvariantAt_eq_zero_of_valuation_eq_one {v : HeightOneSpectrum (𝓞 K)}
    {a b : Kˣ} (h2 : v.valuation K 2 = 1) (ha : v.valuation K a = 1)
    (hb : v.valuation K b = 1) : finiteHilbertInvariantAt K v a b = 0 := by
  -- the residue characteristic of `K_v` is odd, since `2` is a unit of its valuation ring
  have h2' := (v.unitsMap_algebraMap_mem_unitFiltration_zero_iff (Units.mk0 (2 : K) two_ne_zero)).2
    h2
  obtain ⟨u, -, hu⟩ := mem_unitFiltration_iff_exists.1 h2'
  have hp : ¬ ringChar 𝓀[v.adicCompletion K] ∣ 2 := by
    refine IsLocalRing.isUnit_natCast_iff_not_dvd.1 ?_
    have hu2 : ((2 : ℕ) : 𝒪[v.adicCompletion K]) = u := Subtype.ext <| by
      rw [hu, Units.coe_map, Units.val_mk0, MonoidHom.coe_ofClass, map_ofNat]
      norm_cast
    exact hu2 ▸ u.isUnit
  have hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  rw [finiteHilbertInvariantAt_def K v _ _ hζ hζ.neZero'.out.isUnit]
  exact localSymbol_kummerClass_eq_zero_of_mem_unitFiltration hζ _ hp
    ((v.unitsMap_algebraMap_mem_unitFiltration_zero_iff a).2 ha)
    ((v.unitsMap_algebraMap_mem_unitFiltration_zero_iff b).2 hb)

/-- **The Hilbert invariants of a fixed pair have finite support**: for `a, b ∈ Kˣ`, the Hilbert
invariant of `a` and `b` vanishes at all but finitely many finite places. -/
theorem hasFiniteSupport_finiteHilbertInvariantAt (a b : Kˣ) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦ finiteHilbertInvariantAt K v a b).HasFiniteSupport := by
  refine (((HeightOneSpectrum.finite_setOfPred_valuation_ne_one (two_ne_zero' K)).union
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one a.ne_zero)).union
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one b.ne_zero)).subset fun v hv ↦ ?_
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hbad
  exact hv (finiteHilbertInvariantAt_eq_zero_of_valuation_eq_one K hbad.1.1 hbad.1.2 hbad.2)

/-- **The support of the Hilbert invariants** of `a, b ∈ Kˣ`: the finite set of the finite places
at which their Hilbert invariant is nonzero. -/
def finiteHilbertSupport (a b : Kˣ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  Set.Finite.toFinset (s := Function.support fun v ↦ finiteHilbertInvariantAt K v a b)
    (hasFiniteSupport_finiteHilbertInvariantAt K a b)

/-- A finite place lies in the support of the Hilbert invariants of `a` and `b` exactly when
their Hilbert invariant there is nonzero. -/
@[simp]
theorem mem_finiteHilbertSupport {a b : Kˣ} {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ finiteHilbertSupport K a b ↔ finiteHilbertInvariantAt K v a b ≠ 0 :=
  (Set.Finite.mem_toFinset _).trans Function.mem_support

/-- Outside its support, the Hilbert invariant of `a` and `b` vanishes. -/
theorem finiteHilbertInvariantAt_eq_zero_of_notMem {a b : Kˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ finiteHilbertSupport K a b) : finiteHilbertInvariantAt K v a b = 0 :=
  not_not.1 fun h ↦ hv ((mem_finiteHilbertSupport K).2 h)

end TauCeti.ClassFieldTheory
