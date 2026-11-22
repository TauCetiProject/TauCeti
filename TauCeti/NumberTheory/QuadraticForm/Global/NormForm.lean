/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# Local-to-global representation by binary quadratic forms

For a nonzero element `d` of a number field `K`, the binary norm plane `⟨1, -d⟩`, written in
coordinates as `x² - d y²`, represents a scalar `a ∈ K` over `K` if and only if it represents `a`
at every finite and every real place (`QuadraticForm.LocallyRepresentsScalar`).

When `d` is not a square in `K` and `a` is nonzero, `⟨1, -d⟩` is the norm form of the quadratic
field extension `K(√d) / K`, and the arithmetic core is Hasse's norm theorem in coordinates
(`TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion`). At each finite place the
canonical diagonal localization identifies local scalar representation with solvability of
`a = x² - d y²` in `K_v`; at each infinite place the archimedean Hilbert symbol identifies
solvability in `w.Completion` with the real-place Hilbert symbol when `w` is real
(`TauCeti.hilbertSymbol_completion_eq_unitAtRealPlace`) and makes it automatic when `w` is complex
(`TauCeti.hilbertSymbol_completion_eq_one_of_isComplex`). When `d` is a nonzero square in `K`, the
plane `⟨1, -d⟩` is regular and isotropic over `K`, so it already represents every scalar globally.

Reading unit representation of `⟨1, -d⟩` through the norm-equation Hilbert symbol
(`TauCeti.mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one`) yields the local-to-global
triviality criterion for `TauCeti.hilbertSymbol` over number fields.

## Main results

* `QuadraticForm.represents_atFinitePlace_weightedSumSquares_one_neg_iff` and
  `QuadraticForm.represents_atRealPlace_weightedSumSquares_one_neg_iff`: local representation of a
  global scalar by `⟨1, -d⟩` as solvability of `a = x² - d y²` in `K_v` or `ℝ`.
* `QuadraticForm.represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one` and
  `QuadraticForm.represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one`:
  local representation of a global unit by `⟨1, -d⟩` as positivity of the localized Hilbert symbol.
* `QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`: the
  local-to-global principle for scalar representation by `⟨1, -d⟩` for any nonzero `d ∈ K`.
* `TauCeti.hilbertSymbol_eq_one_iff_forall_places` and
  `TauCeti.hilbertSymbol_eq_neg_one_iff_exists_place`: global triviality and nontriviality of the
  Hilbert symbol detected by finite and real places.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer (1999), Chapter VI, §4 (the cyclic Hasse norm
  theorem).
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:23.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §1.1, Proposition 1 (the
  norm-form characterization of the Hilbert symbol), Chapter III, §1.2, Theorem 1 (used in the
  `ℚ₃` worked example), and Chapter IV, §3.2, Theorem 8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  QuadraticMap

universe u

namespace QuadraticForm

section NormPlane

variable {K : Type u} [Field K] [NumberField K]

/-- At a finite place `v`, the localization of `⟨1, -d⟩` represents the image of `a` if and only
if `a = x² - d y²` is solvable in `K_v`. -/
theorem represents_atFinitePlace_weightedSumSquares_one_neg_iff
    (v : HeightOneSpectrum (𝓞 K)) (d a : K) :
    Represents (atFinitePlace (weightedSumSquares K ![1, -d]) v)
        (algebraMap K (v.adicCompletion K) a) ↔
      ∃ x y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) a =
          x ^ 2 - algebraMap K (v.adicCompletion K) d * y ^ 2 := by
  rw [(atFinitePlaceWeightedSumSquares v ![1, -d]).represents_iff]
  have hcoeff : (fun i : Fin 2 => algebraMap K (v.adicCompletion K) (![1, -d] i)) =
      ![1, -algebraMap K (v.adicCompletion K) d] := by
    funext i
    fin_cases i <;> simp
  rw [hcoeff, TauCeti.represents_binary_one_neg_iff]

omit [NumberField K] in
/-- At a real place `w`, the localization of `⟨1, -d⟩` represents the real image of `a` if and
only if `a = x² - d y²` is solvable in `ℝ` along the real embedding of `w`. -/
theorem represents_atRealPlace_weightedSumSquares_one_neg_iff
    (w : {w : InfinitePlace K // w.IsReal}) (d a : K) :
    Represents (atRealPlace (weightedSumSquares K ![1, -d]) w) (embedding_of_isReal w.property a) ↔
      ∃ x y : ℝ, embedding_of_isReal w.property a = x ^ 2 - embedding_of_isReal w.property d * y ^ 2
          := by
  rw [(atRealPlaceWeightedSumSquares w ![1, -d]).represents_iff]
  have hcoeff : (fun i : Fin 2 => embedding_of_isReal w.property (![1, -d] i)) =
      ![1, -embedding_of_isReal w.property d] := by
    funext i
    fin_cases i <;> simp
  rw [hcoeff, TauCeti.represents_binary_one_neg_iff]

/-- At a finite place `v`, the localization of `⟨1, -d⟩` represents the unit `a` if and only if
the local Hilbert symbol `(d_v, a_v)_v` is `1`. -/
theorem represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (d a : Kˣ) :
    Represents (atFinitePlace (weightedSumSquares K ![1, -(d : K)]) v)
        (algebraMap K (v.adicCompletion K) (a : K)) ↔
      TauCeti.hilbertSymbol (v.unitAtFinitePlace d) (v.unitAtFinitePlace a) = 1 := by
  rw [represents_atFinitePlace_weightedSumSquares_one_neg_iff, TauCeti.hilbertSymbol_eq_one_iff]
  simp [unitAtFinitePlace_apply]

omit [NumberField K] in
/-- At a real place `w`, the localization of `⟨1, -d⟩` represents the unit `a` if and only if the
real Hilbert symbol `(d_w, a_w)_w` is `1`. -/
theorem represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one
    (w : {w : InfinitePlace K // w.IsReal}) (d a : Kˣ) :
    Represents (atRealPlace (weightedSumSquares K ![1, -(d : K)]) w)
        (embedding_of_isReal w.property (a : K)) ↔
      TauCeti.hilbertSymbol (TauCeti.unitAtRealPlace w d) (TauCeti.unitAtRealPlace w a) = 1 := by
  rw [represents_atRealPlace_weightedSumSquares_one_neg_iff, TauCeti.hilbertSymbol_eq_one_iff]
  simp [TauCeti.unitAtRealPlace_apply]

/-- **Local-to-global scalar representation for `⟨1, -d⟩`.** For any nonzero element `d` of a
number field `K` (so that the binary plane `⟨1, -d⟩` is regular) and any `a ∈ K`, the form
`⟨1, -d⟩` represents `a` over `K` if and only if it represents `a` at every finite and every real
place. -/
theorem represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar
    {d : K} (hd : d ≠ 0) (a : K) :
    Represents (weightedSumSquares K ![1, -d]) a ↔
      LocallyRepresentsScalar (weightedSumSquares K ![1, -d]) a := by
  by_cases hsq : IsSquare d
  · refine ⟨LocallyRepresentsScalar.of_represents, fun _ => ?_⟩
    let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have hnd : (weightedSumSquares K ![1, -d]).Nondegenerate :=
      nondegenerate_weightedSumSquares fun i => by
        fin_cases i <;> simp [isRegular_iff_ne_zero, hd]
    have hiso : ¬ (weightedSumSquares K ![1, -d]).Anisotropic :=
      mt (TauCeti.anisotropic_binary_one_neg_iff d).mp (not_not.mpr hsq)
    exact represents_of_nondegenerate_of_not_anisotropic _ hnd hiso a
  · refine ⟨LocallyRepresentsScalar.of_represents, fun hloc => ?_⟩
    by_cases ha : a = 0
    · subst ha
      exact represents_zero _
    · let u : Kˣ := Units.mk0 a ha
      let d' : Kˣ := Units.mk0 d hd
      have hu : (u : K) = a := Units.val_mk0 ha
      have hd' : (d' : K) = d := Units.val_mk0 hd
      rw [← hu, TauCeti.represents_binary_one_neg_iff,
        TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion hsq u]
      rw [locallyRepresentsScalar_iff] at hloc
      refine ⟨fun v => ?_, fun w => ?_⟩
      · rw [hu]
        exact (represents_atFinitePlace_weightedSumSquares_one_neg_iff v d a).mp (hloc.1 v)
      · rw [← hd']
        simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using
          (TauCeti.hilbertSymbol_eq_one_iff
            (Units.map (algebraMap K w.Completion).toMonoidHom d')
            (Units.map (algebraMap K w.Completion).toMonoidHom u)).mp <| by
          rcases w.isReal_or_isComplex with hw | hw
          · rw [TauCeti.hilbertSymbol_completion_eq_unitAtRealPlace ⟨w, hw⟩ d' u,
              ← represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one
                ⟨w, hw⟩ d' u, hd', hu]
            exact hloc.2 ⟨w, hw⟩
          · exact TauCeti.hilbertSymbol_completion_eq_one_of_isComplex hw _ _

end NormPlane

end QuadraticForm

namespace TauCeti

open _root_.QuadraticForm

section HilbertSymbol

variable {K : Type u} [Field K] [NumberField K]

/-- **Local-to-global triviality of the Hilbert symbol.** Over a number field `K`, the Hilbert
symbol `(d, a)` of two global units is `1` if and only if its localizations at every finite place
and every real place are `1`. -/
theorem hilbertSymbol_eq_one_iff_forall_places (d a : Kˣ) :
    hilbertSymbol d a = 1 ↔
      (∀ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace d) (v.unitAtFinitePlace a) = 1) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w d) (unitAtRealPlace w a) = 1 := by
  rw [← mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one, mem_unitValueSet,
    represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar d.ne_zero,
    locallyRepresentsScalar_iff]
  exact and_congr
    (forall_congr' fun v =>
      represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one v d a)
    (forall_congr' fun w =>
      represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one w d a)

/-- Over a number field `K`, the Hilbert symbol `(d, a)` is `-1` if and only if it is `-1` at some
finite place or at some real place. -/
theorem hilbertSymbol_eq_neg_one_iff_exists_place (d a : Kˣ) :
    hilbertSymbol d a = -1 ↔
      (∃ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace d) (v.unitAtFinitePlace a) = -1) ∨
      ∃ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w d) (unitAtRealPlace w a) = -1 := by
  rw [← Int.units_ne_iff_eq_neg, ne_eq, hilbertSymbol_eq_one_iff_forall_places, not_and_or]
  simp_rw [not_forall, ← ne_eq, Int.units_ne_iff_eq_neg]

end HilbertSymbol

section Examples

/-- **Worked example.** Over `ℚ`, the sum-of-two-squares plane `⟨1, 1⟩` represents `5 = 1² + 2²`,
hence represents `5` at every finite and real place. -/
example : LocallyRepresentsScalar (weightedSumSquares ℚ ![(1 : ℚ), 1]) 5 := by
  refine LocallyRepresentsScalar.of_represents ?_
  rw [represents_iff, Set.mem_range]
  refine ⟨![1, 2], ?_⟩
  norm_num [weightedSumSquares_apply, Fin.sum_univ_two]

/-- **Worked example.** Over `ℚ`, `⟨1, 1⟩` neither locally nor globally represents `3`: at the
3-adic place, `(-1, 3)_{ℚ₃} = -1` obstructs local representation, and hence global representation
over `ℚ` fails by base change (`LocallyRepresentsScalar.of_represents`). -/
example : ¬ LocallyRepresentsScalar (weightedSumSquares ℚ ![(1 : ℚ), 1]) 3 ∧
    ¬ Represents (weightedSumSquares ℚ ![(1 : ℚ), 1]) 3 := by
  have h1 : ![(1 : ℚ), 1] = ![1, -((-1 : ℚˣ) : ℚ)] := by
    funext i
    fin_cases i <;> simp
  have hnotloc : ¬ LocallyRepresentsScalar (weightedSumSquares ℚ ![(1 : ℚ), 1]) 3 := by
    intro hloc
    let ℓ : Nat.Primes := ⟨3, Nat.prime_three⟩
    let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ℓ
    let u3 : ℚˣ := Units.mk0 3 (by norm_num)
    have hv : Represents
        (atFinitePlace (weightedSumSquares ℚ ![1, -((-1 : ℚˣ) : ℚ)]) v)
        (algebraMap ℚ (v.adicCompletion ℚ) (u3 : ℚ)) := by
      simp only [u3, Units.val_mk0, ← h1]
      exact ((locallyRepresentsScalar_iff _ 3).mp hloc).1 v
    rw [represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one,
      hilbertSymbol_unitAtFinitePlace_rat ℓ (-1) u3] at hv
    have hp : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
    have hpadic : hilbertSymbol (-1 : ℚ_[3]ˣ) (Units.mk0 (3 : ℚ_[3]) (by norm_num)) = -1 :=
      by simpa [TauCeti.padicPrimeUnit_eq_mk0] using
        Padic.hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three 3 rfl
    have heq : Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom (-1 : ℚˣ) = (-1 : ℚ_[3]ˣ) ∧
        Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom u3 =
          Units.mk0 (3 : ℚ_[3]) (by norm_num) := by
      constructor <;> ext <;> simp [ℓ, u3]
    rw [heq.1, heq.2, hpadic] at hv
    exact absurd hv (by decide)
  refine ⟨hnotloc, fun hrep => hnotloc ?_⟩
  exact LocallyRepresentsScalar.of_represents hrep

end Examples

end TauCeti
