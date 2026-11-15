/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
public import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# Local-to-global representation by binary quadratic forms

For a nonzero element `d` of a number field `K`, the binary norm plane `⟨1, -d⟩`, written in
coordinates as `x² - d y²`, represents a scalar `a ∈ K` over `K` if and only if it represents `a`
at every finite and every real place (`QuadraticForm.LocallyRepresentsScalar`).

When `d` is not a square in `K` and `a` is nonzero, `⟨1, -d⟩` is the norm form of the quadratic
field extension `K(√d) / K`, and the arithmetic core is Hasse's norm theorem in coordinates
(`TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion`). At each finite place and
each real place, the canonical diagonal localization identifies local scalar representation with
solvability of `a = x² - d y²` in the completion, reading the real completion through
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`. Complex places impose no condition,
since every element of a complex completion is a square (`y = 0`). When `d` is a nonzero square in
`K`, the plane `⟨1, -d⟩` is regular and isotropic over `K`, so it already represents every scalar
globally.

Diagonalizing an arbitrary regular binary form `Q` over `K` and rescaling by the inverse of its
first diagonal coefficient extends local-to-global scalar representation to every regular
two-dimensional quadratic form over `K`. Reading unit representation of `⟨1, -d⟩` through the
norm-equation Hilbert symbol (`TauCeti.mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one`)
yields the local-to-global triviality criterion for `TauCeti.hilbertSymbol` over number fields.

## Main results

* `QuadraticForm.represents_atFinitePlace_weightedSumSquares_one_neg_iff` and
  `QuadraticForm.represents_atRealPlace_weightedSumSquares_one_neg_iff`: local representation of a
  global scalar by `⟨1, -d⟩` as solvability of `a = x² - d y²` in `K_v` or `ℝ`.
* `QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar_of_not_isSquare`
  and `QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`: the
  local-to-global principle for scalar representation by `⟨1, -d⟩` when `d` is a nonsquare or any
  nonzero scalar.
* `QuadraticForm.mem_unitValueSet_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`: the
  unit-value formulation for `d, a ∈ Kˣ`.
* `QuadraticForm.represents_iff_locallyRepresentsScalar_of_finrank_eq_two` and
  `QuadraticForm.mem_unitValueSet_iff_locallyRepresentsScalar_of_finrank_eq_two`: a regular binary
  quadratic form over a number field represents a scalar (or unit) globally if and only if it
  represents it at every finite and real place.
* `TauCeti.hilbertSymbol_eq_one_iff_forall` and `TauCeti.hilbertSymbol_eq_neg_one_iff_exists`:
  global triviality and nontriviality of the Hilbert symbol detected by finite and real places.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer (1999), Chapter VI, §4 (the cyclic Hasse norm
  theorem).
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:23.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §1.2, Theorem 1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  QuadraticMap

universe u v

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

/-- At a real place `w`, the localization of `⟨1, -d⟩` represents the real image of `a` if and
only if `a = x² - d y²` is solvable in `ℝ` along the real embedding of `w`. -/
theorem represents_atRealPlace_weightedSumSquares_one_neg_iff
    (w : {w : InfinitePlace K // w.IsReal}) (d a : K) :
    Represents (atRealPlace (weightedSumSquares K ![1, -d]) w) (embedding_of_isReal w.2 a) ↔
      ∃ x y : ℝ, embedding_of_isReal w.2 a = x ^ 2 - embedding_of_isReal w.2 d * y ^ 2 := by
  rw [(atRealPlaceWeightedSumSquares w ![1, -d]).represents_iff]
  have hcoeff : (fun i : Fin 2 => embedding_of_isReal w.2 (![1, -d] i)) =
      ![1, -embedding_of_isReal w.2 d] := by
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

/-- At a real place `w`, the localization of `⟨1, -d⟩` represents the unit `a` if and only if the
real Hilbert symbol `(d_w, a_w)_w` is `1`. -/
theorem represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one
    (w : {w : InfinitePlace K // w.IsReal}) (d a : Kˣ) :
    Represents (atRealPlace (weightedSumSquares K ![1, -(d : K)]) w)
        (embedding_of_isReal w.2 (a : K)) ↔
      TauCeti.hilbertSymbol (TauCeti.unitAtRealPlace w d) (TauCeti.unitAtRealPlace w a) = 1 := by
  rw [represents_atRealPlace_weightedSumSquares_one_neg_iff, TauCeti.hilbertSymbol_eq_one_iff]
  simp [TauCeti.unitAtRealPlace_apply]

omit [NumberField K] in
/-- Over the completion at any infinite place `w`, if `w` is real then `a = x² - d y²` transports
along `K_w ≃+* ℝ` to the real equation at `w`; if `w` is complex then `a = x² - d y²` is always
solvable with `y = 0` because `ℂ` is algebraically closed. -/
private theorem exists_sq_sub_mul_sq_infiniteCompletion_of_real
    {w : InfinitePlace K} {d a : K}
    (hreal : ∀ hw : w.IsReal,
      ∃ x y : ℝ, embedding_of_isReal hw a = x ^ 2 - embedding_of_isReal hw d * y ^ 2) :
    ∃ x y : w.Completion,
      algebraMap K w.Completion a = x ^ 2 - algebraMap K w.Completion d * y ^ 2 := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨x, y, hxy⟩ := hreal hw
    let e := Completion.ringEquivRealOfIsReal hw
    refine ⟨e.symm x, e.symm y, e.injective ?_⟩
    rw [map_sub, map_pow, map_mul, map_pow, e.apply_symm_apply, e.apply_symm_apply]
    simpa [e, NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe] using hxy
  · let e := Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (e (algebraMap K w.Completion a))
    refine ⟨e.symm z, 0, e.injective ?_⟩
    simp [pow_two, ← hz]

/-- **The quadratic Hasse norm theorem for `⟨1, -d⟩` with nonsquare `d`.** For a nonsquare `d` in
a number field `K`, the norm form `⟨1, -d⟩` represents `a ∈ K` over `K` if and only if it
represents `a` at every finite and every real place. -/
theorem represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar_of_not_isSquare
    {d : K} (hd : ¬ IsSquare d) (a : K) :
    Represents (weightedSumSquares K ![1, -d]) a ↔
      LocallyRepresentsScalar (weightedSumSquares K ![1, -d]) a := by
  refine ⟨LocallyRepresentsScalar.of_represents, fun hloc => ?_⟩
  by_cases ha : a = 0
  · subst ha
    exact represents_zero _
  · let u : Kˣ := Units.mk0 a ha
    have hu : (u : K) = a := rfl
    rw [← hu, TauCeti.represents_binary_one_neg_iff,
      TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion hd u]
    rw [locallyRepresentsScalar_iff] at hloc
    refine ⟨fun v => (represents_atFinitePlace_weightedSumSquares_one_neg_iff v d a).mp (hloc.1 v),
      fun w => exists_sq_sub_mul_sq_infiniteCompletion_of_real fun hw =>
        (represents_atRealPlace_weightedSumSquares_one_neg_iff ⟨w, hw⟩ d a).mp (hloc.2 ⟨w, hw⟩)⟩

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
  · exact represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar_of_not_isSquare hsq a

/-- **Local-to-global unit representation for `⟨1, -d⟩`.** For units `d, a ∈ Kˣ` of a number field
`K`, `a` lies in the represented-unit value set of `⟨1, -d⟩` if and only if `⟨1, -d⟩` locally
represents `a` at every finite and real place. -/
theorem mem_unitValueSet_weightedSumSquares_one_neg_iff_locallyRepresentsScalar (d a : Kˣ) :
    a ∈ unitValueSet (weightedSumSquares K ![1, -(d : K)]) ↔
      LocallyRepresentsScalar (weightedSumSquares K ![1, -(d : K)]) (a : K) :=
  mem_unitValueSet.trans (represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar
    d.ne_zero (a : K))

/-- **Local-to-global scalar representation for regular binary forms.** Every regular
two-dimensional quadratic form over a number field `K` represents a scalar `a ∈ K` over `K` if and
only if it represents `a` at every finite and every real place. -/
theorem represents_iff_locallyRepresentsScalar_of_finrank_eq_two
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate)
    (hrank : Module.finrank K V = 2) (a : K) :
    Represents Q a ↔ Q.LocallyRepresentsScalar a := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hQw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  let σ : Fin 2 ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  have hre : (weightedSumSquares K w).Equivalent
      (weightedSumSquares K ![(w (σ 0) : K), (w (σ 1) : K)]) := by
    rw [weightedSumSquares_units]
    refine (TauCeti.equivalent_weightedSumSquares_comp (fun i => (w i : K)) σ).trans ?_
    have hfun : ((fun i => (w i : K)) ∘ σ) = ![(w (σ 0) : K), (w (σ 1) : K)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
  have hQbin : Q.Equivalent (weightedSumSquares K ![(w (σ 0) : K), (w (σ 1) : K)]) :=
    hQw.trans hre
  let u₀ : Kˣ := w (σ 0)
  let d : Kˣ := -(u₀⁻¹ * w (σ 1))
  have hscale : weightedSumSquares K ![(u₀ : K), (w (σ 1) : K)] =
      (u₀ : K) • weightedSumSquares K ![1, -(d : K)] := by
    rw [smul_weightedSumSquares]
    congr 1
    funext i
    fin_cases i <;> simp [u₀, d]
  obtain ⟨e⟩ := hQbin
  rw [e.represents_iff, QuadraticMap.Equivalent.locallyRepresentsScalar_iff ⟨e⟩, hscale,
    represents_smul_iff u₀.ne_zero, locallyRepresentsScalar_smul_iff u₀.ne_zero]
  exact represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar d.ne_zero _

/-- A regular binary quadratic form over a number field represents a unit `a ∈ Kˣ` globally if and
only if it represents `a` at every finite and real place. -/
theorem mem_unitValueSet_iff_locallyRepresentsScalar_of_finrank_eq_two
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate)
    (hrank : Module.finrank K V = 2) (a : Kˣ) :
    a ∈ unitValueSet Q ↔ Q.LocallyRepresentsScalar (a : K) :=
  mem_unitValueSet.trans (represents_iff_locallyRepresentsScalar_of_finrank_eq_two hQ hrank (a : K))

end NormPlane

end QuadraticForm

namespace TauCeti

open _root_.QuadraticForm

section HilbertSymbol

variable {K : Type u} [Field K] [NumberField K]

/-- **Local-to-global triviality of the Hilbert symbol.** Over a number field `K`, the Hilbert
symbol `(d, a)` of two global units is `1` if and only if its localizations at every finite place
and every real place are `1`. -/
theorem hilbertSymbol_eq_one_iff_forall (d a : Kˣ) :
    hilbertSymbol d a = 1 ↔
      (∀ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace d) (v.unitAtFinitePlace a) = 1) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w d) (unitAtRealPlace w a) = 1 := by
  rw [← mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one,
    mem_unitValueSet_weightedSumSquares_one_neg_iff_locallyRepresentsScalar,
    locallyRepresentsScalar_iff]
  exact and_congr
    (forall_congr' fun v =>
      represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one v d a)
    (forall_congr' fun w =>
      represents_atRealPlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one w d a)

/-- Over a number field `K`, the Hilbert symbol `(d, a)` is `-1` if and only if it is `-1` at some
finite place or at some real place. -/
theorem hilbertSymbol_eq_neg_one_iff_exists (d a : Kˣ) :
    hilbertSymbol d a = -1 ↔
      (∃ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace d) (v.unitAtFinitePlace a) = -1) ∨
      ∃ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w d) (unitAtRealPlace w a) = -1 := by
  rw [← Int.units_ne_iff_eq_neg, ne_eq, hilbertSymbol_eq_one_iff_forall, not_and_or]
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
3-adic place, `(-1, 3)_{ℚ₃} = -1` obstructs local representation, and the local-to-global adapter
carries this obstruction to `ℚ`. -/
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
      rw [← h1]
      exact ((locallyRepresentsScalar_iff _ 3).mp hloc).1 v
    rw [represents_atFinitePlace_weightedSumSquares_one_neg_iff_hilbertSymbol_eq_one,
      hilbertSymbol_unitAtFinitePlace_rat ℓ (-1) u3] at hv
    have hp : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
    have hpadic : hilbertSymbol (-1 : ℚ_[3]ˣ) (Units.mk0 (3 : ℚ_[3]) (by norm_num)) = -1 :=
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
