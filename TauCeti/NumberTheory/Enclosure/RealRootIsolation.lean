/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Enclosure.Archimedean
public import TauCeti.NumberTheory.Enclosure.RootIsolation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Isolated real roots and their refinements

A real algebraic number used in a certified computation is pinned down by a *real root
isolation*: a nonzero polynomial `g ∈ ℚ[X]` and a closed rational interval `[l, u]` in which `g`
has exactly one real root. The interval is a rational enclosure of that root
(`TauCeti.RealEnclosure`), and the proof that the interval contains no other real root of `g` is
part of the datum.

An isolation can be refined to any precision without changing the root it selects: bisecting the
interval and keeping the half that contains the root gives, at level `n`, a nested subinterval of
width `2⁻ⁿ` times the original width (`TauCeti.RealRootIsolation.refine`), and the subinterval
still isolates the same root because it lies in the original interval. A singleton interval
`[q, q]` stays a singleton. The same bisection refines the rectangle of an exact algebraic datum
of a complex value (`TauCeti.RootIsolation.refineBox`), and the real side of such a
rectangle isolates the value as a real root when the value is real
(`TauCeti.RootIsolation.toRealRootIsolationOfBox`).

Overlapping intervals do not identify roots: `[1, 2]` isolates `√2` as a root of `X² - 2` and
`√3` as a root of `X² - 3`. The root selected by an isolation is fixed by the datum, and is never
read off a numerical approximation.

## Main definitions

* `TauCeti.RealRootIsolation r`: a real enclosure of `r` together with a nonzero polynomial
  `g ∈ ℚ[X]` of which `r` is the only real root in the interval.
* `TauCeti.RealRootIsolation.restrict`: the isolation obtained by shrinking the interval to a
  smaller enclosure of the same root.
* `TauCeti.RealRootIsolation.refine D n`: the refinement of `D` at level `n`, the same polynomial
  with the interval bisected `n` times.
* `TauCeti.RealRootIsolation.ofRat`: the isolation of a rational number `q` by `X - q` and
  `[q, q]`.
* `TauCeti.RootIsolation.toRealRootIsolation`,
  `TauCeti.RootIsolation.toRealRootIsolationOfBox`: the real isolation of a real value read off an
  exact algebraic datum.

## Main results

* `TauCeti.RealRootIsolation.existsUnique`: the interval contains exactly one real root of the
  polynomial; `TauCeti.RealRootIsolation.eq_of_poly_eq_of_interval_eq`: the polynomial and the
  interval determine the isolated root.
* `TauCeti.RealRootIsolation.refine_toRealEnclosure`: the enclosure of the refinement at level
  `n` is `TauCeti.RealEnclosure.refine`, so its interval lies in the original one
  (`TauCeti.RealEnclosure.refine_interval_le`), the intervals are nested
  (`TauCeti.RealEnclosure.refine_interval_antitone`) and the width is `2⁻ⁿ` times the original
  width (`TauCeti.RealEnclosure.length_refine`).
* `TauCeti.RealRootIsolation.nonempty_iff_isAlgebraic`: a real number has an isolation exactly
  when it is algebraic over `ℚ`.

## References

* B. M. M. de Weger, *Algorithms for Diophantine equations*, CWI Tract 65, 1989, §2.5, printed
  pp. 32–34 (numerical approximation of roots in Diophantine computations).
-/

public section

open Polynomial

namespace TauCeti

/-- A *real root isolation* of `r : ℝ`: a rational enclosure `[l, u]` of `r` together with a
nonzero polynomial `g ∈ ℚ[X]` such that `r` is the only real root of `g` in `[l, u]`. -/
@[ext]
structure RealRootIsolation (r : ℝ) extends RealEnclosure r where
  /-- The isolating polynomial. -/
  poly : ℚ[X]
  /-- The isolating polynomial is nonzero. -/
  poly_ne_zero : poly ≠ 0
  /-- The isolating polynomial vanishes at `r`. -/
  aeval_poly : aeval r poly = 0
  /-- Every real root of the isolating polynomial in the interval is `r`. -/
  eq_of_mem_Icc : ∀ u ∈ Set.Icc (interval.fst : ℝ) interval.snd, aeval u poly = 0 → u = r

namespace RealRootIsolation

attribute [simp] aeval_poly

variable {r r' : ℝ}

/-- The interval of an isolation contains exactly one real root of the isolating polynomial. -/
theorem existsUnique (D : RealRootIsolation r) :
    ∃! u : ℝ, u ∈ Set.Icc (D.interval.fst : ℝ) D.interval.snd ∧ aeval u D.poly = 0 :=
  ⟨r, ⟨D.mem_Icc, D.aeval_poly⟩, fun u hu => D.eq_of_mem_Icc u hu.1 hu.2⟩

/-- The polynomial and the interval of an isolation determine the isolated root. -/
theorem eq_of_poly_eq_of_interval_eq (D : RealRootIsolation r) (D' : RealRootIsolation r')
    (hpoly : D.poly = D'.poly) (hinterval : D.interval = D'.interval) : r = r' :=
  (D.eq_of_mem_Icc r' (hinterval ▸ D'.mem_Icc) (hpoly ▸ D'.aeval_poly)).symm

/-- The isolation of a rational number `q` by the polynomial `X - q` and the singleton interval
`[q, q]`. -/
noncomputable def ofRat (q : ℚ) : RealRootIsolation q where
  toRealEnclosure := RealEnclosure.ofRat q
  poly := X - C q
  poly_ne_zero := X_sub_C_ne_zero q
  aeval_poly := by simp
  eq_of_mem_Icc u hu _ := by
    simpa [RealEnclosure.ofRat_interval, NonemptyInterval.pure] using hu

@[simp]
theorem ofRat_toRealEnclosure (q : ℚ) : (ofRat q).toRealEnclosure = RealEnclosure.ofRat q :=
  (rfl)

@[simp]
theorem ofRat_poly (q : ℚ) : (ofRat q).poly = X - C q :=
  (rfl)

/-- Shrinking the interval of an isolation to a smaller enclosure of the same number gives an
isolation by the same polynomial. -/
def restrict (D : RealRootIsolation r) (E : RealEnclosure r) (h : E.interval ≤ D.interval) :
    RealRootIsolation r where
  toRealEnclosure := E
  poly := D.poly
  poly_ne_zero := D.poly_ne_zero
  aeval_poly := D.aeval_poly
  eq_of_mem_Icc u hu := D.eq_of_mem_Icc u (NonemptyInterval.Icc_ratCast_subset_Icc_ratCast h hu)

@[simp]
theorem restrict_toRealEnclosure (D : RealRootIsolation r) (E : RealEnclosure r)
    (h : E.interval ≤ D.interval) : (D.restrict E h).toRealEnclosure = E :=
  (rfl)

@[simp]
theorem restrict_poly (D : RealRootIsolation r) (E : RealEnclosure r)
    (h : E.interval ≤ D.interval) : (D.restrict E h).poly = D.poly :=
  (rfl)

/-- The refinement of an isolation at level `n`: the same polynomial, with the interval bisected
`n` times, keeping each time the half containing the root. It isolates the same root; its
interval lies in the original one and has width `2⁻ⁿ` times the original width. -/
noncomputable def refine (D : RealRootIsolation r) (n : ℕ) : RealRootIsolation r :=
  D.restrict (D.toRealEnclosure.refine n) (D.toRealEnclosure.refine_interval_le n)

@[simp]
theorem refine_toRealEnclosure (D : RealRootIsolation r) (n : ℕ) :
    (D.refine n).toRealEnclosure = D.toRealEnclosure.refine n :=
  (rfl)

@[simp]
theorem refine_poly (D : RealRootIsolation r) (n : ℕ) : (D.refine n).poly = D.poly :=
  (rfl)

@[simp]
theorem refine_zero (D : RealRootIsolation r) : D.refine 0 = D :=
  RealRootIsolation.ext (by simp) (by simp)

end RealRootIsolation

namespace RootIsolation

variable {K : Type*} [Field K] [Algebra ℚ K] {σ : K →+* ℂ} {z : K}

/-- If `σ z` is real, every rational enclosure of `Re (σ z)` whose real points all lie in the
region of an isolation of `z` isolates `Re (σ z)` as a real root of the same polynomial. -/
def toRealRootIsolation (D : RootIsolation σ z) (hz : (σ z).im = 0)
    (E : RealEnclosure (σ z).re)
    (hE : ∀ t ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd, (t : ℂ) ∈ D.region.toSet) :
    RealRootIsolation (σ z).re :=
  -- Evaluation of a rational polynomial commutes with the embedding `ℝ → ℂ`.
  have key (t : ℝ) : ((aeval t D.poly : ℝ) : ℂ) = aeval (t : ℂ) D.poly :=
    (aeval_algHom_apply Complex.ofRealHom.toRatAlgHom t D.poly).symm
  { toRealEnclosure := E
    poly := D.poly
    poly_ne_zero := D.poly_ne_zero
    aeval_poly := by
      have hre : ((σ z).re : ℂ) = σ z := Complex.ext (by simp) (by simp [hz])
      exact Complex.ofReal_injective (by rw [key, hre, D.aeval_apply_poly, Complex.ofReal_zero])
    eq_of_mem_Icc u hu h0 := by
      have := D.eq_of_mem_region u (hE u hu) (by rw [← key, h0, Complex.ofReal_zero])
      simpa using congrArg Complex.re this }

@[simp]
theorem toRealRootIsolation_toRealEnclosure (D : RootIsolation σ z) (hz : (σ z).im = 0)
    (E : RealEnclosure (σ z).re)
    (hE : ∀ t ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd, (t : ℂ) ∈ D.region.toSet) :
    (D.toRealRootIsolation hz E hE).toRealEnclosure = E :=
  (rfl)

@[simp]
theorem toRealRootIsolation_poly (D : RootIsolation σ z) (hz : (σ z).im = 0)
    (E : RealEnclosure (σ z).re)
    (hE : ∀ t ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd, (t : ℂ) ∈ D.region.toSet) :
    (D.toRealRootIsolation hz E hE).poly = D.poly :=
  (rfl)

/-- If `σ z` is real, the real side `R` of the rectangle `R × J` of an isolation of `z` isolates
`Re (σ z)` as a real root of the same polynomial. -/
def toRealRootIsolationOfBox (D : RootIsolation σ z) (hz : (σ z).im = 0)
    {R J : NonemptyInterval ℚ} (h : D.region = .box R J) : RealRootIsolation (σ z).re :=
  D.toRealRootIsolation hz (D.toComplexEnclosureOfBox h).re fun t ht => by
    rw [h, RationalRegion.mem_toSet_box]
    exact ⟨by simpa using ht, by simpa [hz] using (D.toComplexEnclosureOfBox h).im.mem_Icc⟩

@[simp]
theorem toRealRootIsolationOfBox_interval (D : RootIsolation σ z) (hz : (σ z).im = 0)
    {R J : NonemptyInterval ℚ} (h : D.region = .box R J) :
    (D.toRealRootIsolationOfBox hz h).interval = R :=
  D.toComplexEnclosureOfBox_re_interval h

@[simp]
theorem toRealRootIsolationOfBox_poly (D : RootIsolation σ z) (hz : (σ z).im = 0)
    {R J : NonemptyInterval ℚ} (h : D.region = .box R J) :
    (D.toRealRootIsolationOfBox hz h).poly = D.poly :=
  (rfl)

end RootIsolation

namespace RealRootIsolation

/-- A real number has a real root isolation exactly when it is algebraic over `ℚ`. -/
theorem nonempty_iff_isAlgebraic {r : ℝ} : Nonempty (RealRootIsolation r) ↔ IsAlgebraic ℚ r := by
  refine ⟨fun ⟨D⟩ => ⟨D.poly, D.poly_ne_zero, D.aeval_poly⟩, fun hr => ?_⟩
  -- An interval isolation of `r` as a root of its minimal polynomial, viewed in `ℂ`.
  obtain ⟨J, D, -, hJ, hmem, -⟩ := RootIsolation.exists_interval (σ := Complex.ofRealHom)
    (minpoly.irreducible hr.isIntegral).squarefree (minpoly.aeval ℚ r) (by simp) Filter.univ_mem
  exact ⟨D.toRealRootIsolation (by simp) ⟨J, hmem.1.le, hmem.2.le⟩ fun t ht => by
    rw [hJ, RationalRegion.mem_toSet_interval]
    exact ⟨by simp, by simpa using ht⟩⟩

end RealRootIsolation

/-! ### Examples

The following checks illustrate the conventions. For `X² - 2` and `[1, 2]`, the interval
`[11/8, 3/2]` meets the width bound `2⁻³ · 1` of a refinement at level `3`, while `[1, 3/2]` does
not; `[-2, 2]` does not isolate `√2` as a root of `X² - 2`, since it also contains `-√2`. For
`X - q` and `[q, q]` the refinement at every level is `[q, q]`. For `X - 1/2` and `[0, 1]` the
singleton `[1/2, 1/2]` has every absolute precision while `[0, 1]` does not have precision `1`.
The zero polynomial has exactly one real root in `[a, a]`, but it isolates nothing. -/

namespace RealRootIsolation

/-- The isolation of `√2` by `X² - 2` and the interval `[l, u]`, for `0 ≤ l ≤ √2 ≤ u`. -/
private noncomputable def sqrtTwo (I : NonemptyInterval ℚ) (hl : 0 ≤ I.fst)
    (hl' : (I.fst : ℝ) ≤ √2) (hu : √2 ≤ (I.snd : ℝ)) : RealRootIsolation √2 where
  interval := I
  fst_le := hl'
  le_snd := hu
  poly := X ^ 2 - C 2
  poly_ne_zero := X_pow_sub_C_ne_zero two_pos 2
  aeval_poly := by simp
  eq_of_mem_Icc u hu h0 := by
    have hu0 : 0 ≤ u := le_trans (by exact_mod_cast hl) hu.1
    have hu2 : u ^ 2 = 2 := by simpa [sub_eq_zero] using h0
    rw [← Real.sqrt_sq hu0, hu2]

private theorem sqrt_two_mem {a b : ℚ} (ha2 : a ^ 2 ≤ 2) (hb : 2 ≤ b ^ 2)
    (hb0 : 0 ≤ b) : (a : ℝ) ≤ √2 ∧ √2 ≤ (b : ℝ) :=
  ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast ha2),
    (Real.sqrt_le_left (by exact_mod_cast hb0)).mpr (by exact_mod_cast hb)⟩

/-- `[11/8, 3/2]` isolates `√2` for `X² - 2` inside `[1, 2]`, with width `2⁻³` times the width
of `[1, 2]`; the subinterval `[1, 3/2]` misses that width bound. -/
example : ∃ D D' : RealRootIsolation √2, D.poly = X ^ 2 - C 2 ∧
    D.interval = ⟨(1, 2), by norm_num⟩ ∧ D'.interval = ⟨(11 / 8, 3 / 2), by norm_num⟩ ∧
    D'.poly = D.poly ∧ D'.interval ≤ D.interval ∧
    D'.interval.length ≤ (2 ^ 3)⁻¹ * D.interval.length ∧
    ¬ (⟨(1, 3 / 2), by norm_num⟩ : NonemptyInterval ℚ).length ≤
      (2 ^ 3)⁻¹ * D.interval.length := by
  have h1 := sqrt_two_mem (a := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 := sqrt_two_mem (a := 11 / 8) (b := 3 / 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨sqrtTwo _ (by norm_num) h1.1 h1.2, sqrtTwo _ (by norm_num) h2.1 h2.2, rfl, rfl, rfl,
    rfl, ?_, ?_, ?_⟩ <;>
  simp [sqrtTwo, NonemptyInterval.le_def, NonemptyInterval.length] <;> norm_num

/-- `[-2, 2]` is not an isolating interval of `√2` for `X² - 2`: it also contains `-√2`. -/
example : ¬ ∃ D : RealRootIsolation √2, D.poly = X ^ 2 - C 2 ∧
    D.interval = ⟨(-2, 2), by norm_num⟩ := by
  rintro ⟨D, hpoly, hint⟩
  have hpos : 0 < √2 := by positivity
  have := D.eq_of_mem_Icc (-√2) (by simp [hint]; linarith)
    (by simp [hpoly])
  linarith

/-- For `X - q` and `[q, q]`, the refinement at every level is `[q, q]`. -/
example (q : ℚ) (n : ℕ) : ((ofRat q).refine n).interval = NonemptyInterval.pure q := by
  simpa using (RealEnclosure.ofRat q).refine_interval_of_length_eq_zero (by simp) n

/-- For `X - 1/2` and `[0, 1]`, the singleton `[1/2, 1/2]` isolates the same root with every
absolute precision, while `[0, 1]` does not have absolute precision `1`. -/
example : ∃ D D' : RealRootIsolation ((1 / 2 : ℚ) : ℝ), D.poly = X - C (1 / 2) ∧
    D.interval = ⟨(0, 1), by norm_num⟩ ∧ D'.poly = D.poly ∧
    D'.interval = NonemptyInterval.pure (1 / 2) ∧ D'.interval ≤ D.interval ∧
    (∀ n, D'.HasPrecision n) ∧ ¬ D.HasPrecision 1 := by
  let D : RealRootIsolation ((1 / 2 : ℚ) : ℝ) :=
    { interval := ⟨(0, 1), by norm_num⟩
      fst_le := by norm_num
      le_snd := by norm_num
      poly := X - C (1 / 2)
      poly_ne_zero := X_sub_C_ne_zero _
      aeval_poly := by simp
      eq_of_mem_Icc := fun u _ h0 => by simpa [sub_eq_zero] using h0 }
  have hle : (RealEnclosure.ofRat (1 / 2)).interval ≤ D.interval := by
    simp [D, NonemptyInterval.le_def]
    norm_num
  refine ⟨D, D.restrict _ hle, rfl, rfl, rfl, by simp, by simpa using hle, fun n => by simp, ?_⟩
  simp [D, RealEnclosure.hasPrecision_iff, NonemptyInterval.length]
  norm_num

/-- The zero polynomial has exactly one real root in a singleton interval `[a, a]`, but an
isolation requires a nonzero polynomial. -/
example (a : ℚ) : (∃! u : ℝ, u ∈ Set.Icc (a : ℝ) a ∧ aeval u (0 : ℚ[X]) = 0) ∧
    ∀ D : RealRootIsolation a, D.poly ≠ 0 :=
  ⟨⟨a, by simp, fun u hu => by simpa using hu.1⟩, fun D => D.poly_ne_zero⟩

/-- The refinement at level `n` is an enclosure of the same root whose width is at most `2⁻ⁿ`
times the original width. -/
example {r : ℝ} (D : RealRootIsolation r) (n : ℕ) :
    (D.refine n).interval ≤ D.interval ∧
      (D.refine n).interval.length ≤ (2 ^ n)⁻¹ * D.interval.length := by
  simp [RealEnclosure.refine_interval_le, div_eq_inv_mul]

end RealRootIsolation

end TauCeti
