/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Function
public import TauCeti.Analysis.Convex.Sequence.Basic
import Mathlib.Tactic.Linarith

/-!
# Piecewise-affine interpolation of height sequences

A real sequence `f : ℕ → ℝ` has a canonical piecewise-affine interpolation
`linearInterpolate f : ℝ → ℝ`, affine on every interval `[n, n + 1]` and equal to `f n`
at each natural number `n`. For a height sequence `h : ℕ → WithTop ℝ`, the real
points whose floor and ceiling have finite height form `interpolationDomain h`, and the
interpolation of its real heights is considered only there. When the finite domain is
order connected, this is the real interval that it spans.

The main theorem identifies discrete convexity with real convexity of this
interpolation on that domain. This lets results about `ConvexOn` be imported for
convex height sequences, while the discrete predicate `IsConvexSeq` remains the one
used for coefficient arguments. In the convex case, the domain is the spanned real
interval, not just the set of integer points. The interpolation is only one convex extension: for
`h n = n ^ 2`, both it and `x ↦ x ^ 2` are convex functions on `[0, ∞)` extending the
same heights, and `isConvexSeq_of_convexOn` accepts any such extension.

## Main results

* `linearInterpolate_natCast`: the interpolation recovers the sequence at integers.
* `convex_interpolationDomain_iff`: the real domain is an interval exactly when the
  finite domain of the heights is order connected.
* `isConvexSeq_iff_convexOn_linearInterpolate`: a height sequence is convex exactly
  when its interpolation is convex on `interpolationDomain h`, with the specialisations
  `isConvexSeq_iff_convexOn_Icc` for finite domains (including singletons and the empty
  domain) and `isConvexSeq_iff_convexOn_Ici` for half-lines.
* `isConvexSeq_of_convexOn`: heights sampled from any convex function on a convex set
  of reals form a convex height sequence.
* `le_iff_linearInterpolate_le` and `eq_iff_linearInterpolate_eq`: interpolation
  identifies the pointwise order and equality of height sequences.
-/

public section

open Set

namespace TauCeti

/-! ### Interpolation of real sequences -/

/-- The piecewise-affine interpolation of a real sequence: on each interval `[n, n + 1]`
it is the affine function through `(n, f n)` and `(n + 1, f (n + 1))`. At negative
arguments it continues the first edge affinely, so only its values on `[0, ∞)` are
determined by the graph of `f`. -/
noncomputable def linearInterpolate (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  f ⌊x⌋₊ + (x - ⌊x⌋₊) * (f (⌊x⌋₊ + 1) - f ⌊x⌋₊)

/-- The interpolation at `x` is computed on the unit interval starting at `⌊x⌋₊`. -/
theorem linearInterpolate_def (f : ℕ → ℝ) (x : ℝ) :
    linearInterpolate f x = f ⌊x⌋₊ + (x - ⌊x⌋₊) * (f (⌊x⌋₊ + 1) - f ⌊x⌋₊) := (rfl)

/-- The interpolation recovers the sequence at natural numbers. -/
@[simp]
theorem linearInterpolate_natCast (f : ℕ → ℝ) (n : ℕ) : linearInterpolate f n = f n := by
  simp [linearInterpolate_def]

/-- On the closed unit interval `[n, n + 1]` the interpolation is the affine function
through the two endpoint values, including at the right endpoint. -/
theorem linearInterpolate_of_mem_Icc (f : ℕ → ℝ) {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) (n + 1)) :
    linearInterpolate f x = f n + (x - n) * (f (n + 1) - f n) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · rw [linearInterpolate_def,
      (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hx.1)).2 ⟨hx.1, hlt⟩]
  · rw [← Nat.cast_succ, linearInterpolate_natCast]
    push_cast
    ring

/-- The interpolation of an affine sequence is the same affine function on all of `ℝ`. -/
@[simp]
theorem linearInterpolate_affine (c m x : ℝ) :
    linearInterpolate (fun n => c + m * n) x = c + m * x := by
  simp only [linearInterpolate_def, Nat.cast_add, Nat.cast_one]
  ring

/-- At a nonnegative argument, the interpolation is monotone in the two values of the
sequence at the floor and the ceiling of the argument; no other values are used. -/
theorem linearInterpolate_le_linearInterpolate {f g : ℕ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hfloor : f ⌊x⌋₊ ≤ g ⌊x⌋₊) (hceil : f ⌈x⌉₊ ≤ g ⌈x⌉₊) :
    linearInterpolate f x ≤ linearInterpolate g x := by
  rcases (Nat.floor_le_ceil x).lt_or_eq with hlt | heq
  · have hc : ⌈x⌉₊ = ⌊x⌋₊ + 1 := le_antisymm (Nat.ceil_le_floor_add_one x) hlt
    rw [hc] at hceil
    have ht₀ : 0 ≤ x - ⌊x⌋₊ := sub_nonneg.2 (Nat.floor_le hx)
    have ht₁ : 0 ≤ 1 - (x - ⌊x⌋₊) := by linarith [Nat.lt_floor_add_one x]
    simp only [linearInterpolate_def]
    nlinarith [mul_le_mul_of_nonneg_left hfloor ht₁, mul_le_mul_of_nonneg_left hceil ht₀]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = n :=
      ⟨⌊x⌋₊, le_antisymm (heq ▸ Nat.le_ceil x) (Nat.floor_le hx)⟩
    simpa using hfloor

/-- The interpolation is monotone in the sequence at nonnegative arguments. -/
theorem linearInterpolate_mono {f g : ℕ → ℝ} (hfg : f ≤ g) {x : ℝ} (hx : 0 ≤ x) :
    linearInterpolate f x ≤ linearInterpolate g x :=
  linearInterpolate_le_linearInterpolate hx (hfg _) (hfg _)

/-! ### The real domain of a height sequence -/

/-- The interpolation domain of a height sequence: the nonnegative reals whose floor and
ceiling both carry finite heights. When the finite domain is order connected, this is the
real interval that it spans; in particular, integer domains `[l, u]` and `[l, ∞)` give the
corresponding real intervals. -/
def interpolationDomain (h : ℕ → WithTop ℝ) : Set ℝ :=
  {x | 0 ≤ x ∧ h ⌊x⌋₊ ≠ ⊤ ∧ h ⌈x⌉₊ ≠ ⊤}

variable {h g : ℕ → WithTop ℝ}

/-- A real point lies in the interpolation domain when it is nonnegative and the heights
at its floor and ceiling are finite. -/
theorem mem_interpolationDomain {x : ℝ} :
    x ∈ interpolationDomain h ↔ 0 ≤ x ∧ h ⌊x⌋₊ ≠ ⊤ ∧ h ⌈x⌉₊ ≠ ⊤ := Iff.rfl

/-- A natural number lies in the interpolation domain exactly when its height is finite. -/
@[simp]
theorem natCast_mem_interpolationDomain {n : ℕ} :
    (n : ℝ) ∈ interpolationDomain h ↔ h n ≠ ⊤ := by
  simp [mem_interpolationDomain]

/-- The empty polygon has empty interpolation domain. -/
@[simp]
theorem interpolationDomain_top : interpolationDomain (⊤ : ℕ → WithTop ℝ) = ∅ := by
  ext x
  simp [mem_interpolationDomain]

/-- If the finite domain is the integer interval `[l, u]`, the interpolation domain is the
real interval `[l, u]`. This includes the singleton `l = u` and the empty case `u < l`. -/
theorem interpolationDomain_eq_Icc {l u : ℕ} (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ u) :
    interpolationDomain h = Icc (l : ℝ) u := by
  ext x
  simp only [mem_interpolationDomain, hdom, mem_Icc]
  constructor
  · rintro ⟨hx, ⟨hl, -⟩, -, hu⟩
    exact ⟨(Nat.cast_le.2 hl).trans (Nat.floor_le hx), (Nat.le_ceil x).trans (Nat.cast_le.2 hu)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨(Nat.cast_nonneg l).trans hl,
      ⟨Nat.le_floor hl, (Nat.floor_le_ceil x).trans (Nat.ceil_le.2 hu)⟩,
      (Nat.le_floor hl).trans (Nat.floor_le_ceil x), Nat.ceil_le.2 hu⟩

/-- If the finite domain is the integer half-line `[l, ∞)`, the interpolation domain is
the real half-line `[l, ∞)`. -/
theorem interpolationDomain_eq_Ici {l : ℕ} (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n) :
    interpolationDomain h = Ici (l : ℝ) := by
  ext x
  simp only [mem_interpolationDomain, hdom, mem_Ici]
  constructor
  · rintro ⟨hx, hl, -⟩
    exact (Nat.cast_le.2 hl).trans (Nat.floor_le hx)
  · intro hl
    exact ⟨(Nat.cast_nonneg l).trans hl, Nat.le_floor hl,
      (Nat.le_floor hl).trans (Nat.floor_le_ceil x)⟩

/-- The interpolation domain is a real interval exactly when the finite domain of the
heights is order connected. -/
theorem convex_interpolationDomain_iff :
    Convex ℝ (interpolationDomain h) ↔ OrdConnected {n | h n ≠ ⊤} := by
  rw [convex_iff_ordConnected]
  constructor
  · refine fun hD => ⟨fun i hi j hj k hk => ?_⟩
    exact natCast_mem_interpolationDomain.1 (hD.out (natCast_mem_interpolationDomain.2 hi)
      (natCast_mem_interpolationDomain.2 hj) ⟨Nat.cast_le.2 hk.1, Nat.cast_le.2 hk.2⟩)
  · refine fun hD => ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨hx0, hxf, -⟩ := mem_interpolationDomain.1 hx
    obtain ⟨-, -, hyc⟩ := mem_interpolationDomain.1 hy
    have hfl : ⌊x⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono hz.1
    have hce : ⌈z⌉₊ ≤ ⌈y⌉₊ := Nat.ceil_mono hz.2
    exact mem_interpolationDomain.2 ⟨hx0.trans hz.1,
      hD.out hxf hyc ⟨hfl, (Nat.floor_le_ceil z).trans hce⟩,
      hD.out hxf hyc ⟨hfl.trans (Nat.floor_le_ceil z), hce⟩⟩

/-! ### Order and equality through interpolation -/

/-- Heights are ordered pointwise exactly when the larger sequence has the smaller
interpolation domain and, on that domain, the larger interpolation. No convexity is
needed, and infinite heights are compared through the domain inclusion. -/
theorem le_iff_linearInterpolate_le :
    h ≤ g ↔ interpolationDomain g ⊆ interpolationDomain h ∧
      ∀ x ∈ interpolationDomain g,
        linearInterpolate (fun n => (h n).untop₀) x ≤
          linearInterpolate (fun n => (g n).untop₀) x := by
  constructor
  · intro hhg
    have hsub : interpolationDomain g ⊆ interpolationDomain h := fun x hx => by
      obtain ⟨hx0, hfl, hce⟩ := mem_interpolationDomain.1 hx
      exact mem_interpolationDomain.2
        ⟨hx0, ne_top_of_le_ne_top hfl (hhg _), ne_top_of_le_ne_top hce (hhg _)⟩
    refine ⟨hsub, fun x hx => ?_⟩
    obtain ⟨hx0, hfl, hce⟩ := mem_interpolationDomain.1 hx
    exact linearInterpolate_le_linearInterpolate hx0
      (WithTop.untop₀_le_untop₀ hfl (hhg _)) (WithTop.untop₀_le_untop₀ hce (hhg _))
  · rintro ⟨hsub, hle⟩ n
    by_cases hn : g n = ⊤
    · simp [hn]
    have hn' : h n ≠ ⊤ :=
      natCast_mem_interpolationDomain.1 (hsub (natCast_mem_interpolationDomain.2 hn))
    have := hle n (natCast_mem_interpolationDomain.2 hn)
    rw [linearInterpolate_natCast, linearInterpolate_natCast] at this
    exact WithTop.le_of_untop₀_le_untop₀ hn' this

/-- Height sequences are equal exactly when they have the same interpolation domain and
their interpolations agree there. -/
theorem eq_iff_linearInterpolate_eq :
    h = g ↔ interpolationDomain h = interpolationDomain g ∧
      EqOn (linearInterpolate fun n => (h n).untop₀)
        (linearInterpolate fun n => (g n).untop₀) (interpolationDomain h) := by
  refine ⟨fun hhg => hhg ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨hD, hEq⟩ => le_antisymm ?_ ?_⟩
  · exact le_iff_linearInterpolate_le.2 ⟨hD.symm.subset, fun x hx => (hEq (hD ▸ hx)).le⟩
  · exact le_iff_linearInterpolate_le.2 ⟨hD.subset, fun x hx => (hEq hx).ge⟩

/-! ### Convexity through interpolation -/

/-- At every real point of the domain, a convex height sequence has an affine minorant
on the integers whose value there is the interpolated height. Between two consecutive
finite heights it is the line through that edge. -/
theorem IsConvexSeq.exists_affine_minorant_eq_linearInterpolate (hh : IsConvexSeq h)
    {x : ℝ} (hx : x ∈ interpolationDomain h) :
    ∃ c m : ℝ, (∀ n : ℕ, ((c + m * n : ℝ) : WithTop ℝ) ≤ h n) ∧
      c + m * x = linearInterpolate (fun n => (h n).untop₀) x := by
  obtain ⟨hx0, hfl, hce⟩ := mem_interpolationDomain.1 hx
  by_cases hedge : h (⌊x⌋₊ + 1) = ⊤
  · -- The ceiling is finite but the next height is not, so `x` is an integer.
    have hc : ⌈x⌉₊ = ⌊x⌋₊ := le_antisymm
      (Nat.lt_succ_iff.1 ((Nat.ceil_le_floor_add_one x).lt_of_ne fun hc => hce (hc ▸ hedge)))
      (Nat.floor_le_ceil x)
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = n :=
      ⟨⌊x⌋₊, le_antisymm (hc ▸ Nat.le_ceil x) (Nat.floor_le hx0)⟩
    rw [Nat.floor_natCast] at hfl
    obtain ⟨c, m, hline, heq⟩ := hh.exists_affine_minorant_eq hfl
    exact ⟨c, m, hline, by rw [linearInterpolate_natCast, heq]⟩
  · refine ⟨(h ⌊x⌋₊).untop₀ - unitSlope h ⌊x⌋₊ * ⌊x⌋₊, unitSlope h ⌊x⌋₊, fun n => ?_, ?_⟩
    · convert hh.supportingLine_le hfl hedge n using 2
      ring
    · rw [linearInterpolate_def, unitSlope_def]
      ring

/-- The interpolation of a convex height sequence is convex on its real domain. -/
theorem IsConvexSeq.convexOn_linearInterpolate (hh : IsConvexSeq h) :
    ConvexOn ℝ (interpolationDomain h) (linearInterpolate fun n => (h n).untop₀) := by
  have hD := convex_interpolationDomain_iff.2 hh.ordConnected
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨c, m, hline, heq⟩ :=
    hh.exists_affine_minorant_eq_linearInterpolate (hD hx hy ha hb hab)
  -- The affine minorant stays below the interpolation on the whole real domain.
  have hbelow : ∀ z ∈ interpolationDomain h,
      c + m * z ≤ linearInterpolate (fun n => (h n).untop₀) z := fun z hz => by
    have := (le_iff_linearInterpolate_le.1 hline).2 z hz
    simpa only [WithTop.untop₀_coe, linearInterpolate_affine] using this
  have hx' := mul_le_mul_of_nonneg_left (hbelow x hx) ha
  have hy' := mul_le_mul_of_nonneg_left (hbelow y hy) hb
  rw [← heq, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  nlinarith

/-- Heights sampled at the integer points of a convex set of reals from a convex function
form a convex height sequence. The finite domain must be exactly the set of natural
numbers in that set. -/
theorem isConvexSeq_of_convexOn {s : Set ℝ} {F : ℝ → ℝ} (hF : ConvexOn ℝ s F)
    (hs : ∀ n : ℕ, h n ≠ ⊤ ↔ (n : ℝ) ∈ s) (hFh : ∀ n, h n ≠ ⊤ → F n = (h n).untop₀) :
    IsConvexSeq h := by
  have hsc := convex_iff_ordConnected.1 hF.1
  have hD : OrdConnected {n | h n ≠ ⊤} := ⟨fun i hi j hj k hk =>
    (hs k).2 (hsc.out ((hs i).1 hi) ((hs j).1 hj) ⟨Nat.cast_le.2 hk.1, Nat.cast_le.2 hk.2⟩)⟩
  refine isConvexSeq_iff_two_mul_le.2 ⟨hD, fun n hn hn₂ => ?_⟩
  have hn₁ : h (n + 1) ≠ ⊤ := hD.out hn hn₂ ⟨by omega, by omega⟩
  have hmid := hF.2 ((hs n).1 hn) ((hs _).1 hn₂) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • (n : ℝ) + (1 / 2 : ℝ) • ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [e, smul_eq_mul, smul_eq_mul, hFh n hn, hFh _ hn₁, hFh _ hn₂] at hmid
  linarith

/-- **Convexity through interpolation.** A height sequence is convex exactly when the
piecewise-affine interpolation of its real heights is convex on `interpolationDomain h`.
For a convex height sequence this domain is the real interval spanned by its finite domain.
The empty and singleton domains are included. -/
theorem isConvexSeq_iff_convexOn_linearInterpolate :
    IsConvexSeq h ↔
      ConvexOn ℝ (interpolationDomain h) (linearInterpolate fun n => (h n).untop₀) :=
  ⟨IsConvexSeq.convexOn_linearInterpolate, fun hF => isConvexSeq_of_convexOn hF
    (fun _ => natCast_mem_interpolationDomain.symm) fun n _ => linearInterpolate_natCast _ n⟩

/-- A height sequence is convex exactly when some function on `interpolationDomain h` is
convex there and takes its heights at the integer points. For a convex height sequence,
this domain is the real interval spanned by its finite domain. Such an extension is not
unique; the interpolation is one choice. -/
theorem isConvexSeq_iff_exists_convexOn :
    IsConvexSeq h ↔ ∃ F : ℝ → ℝ, ConvexOn ℝ (interpolationDomain h) F ∧
      ∀ n, h n ≠ ⊤ → F n = (h n).untop₀ :=
  ⟨fun hh => ⟨_, hh.convexOn_linearInterpolate, fun n _ => linearInterpolate_natCast _ n⟩,
    fun ⟨_, hF, hFh⟩ => isConvexSeq_of_convexOn hF
      (fun _ => natCast_mem_interpolationDomain.symm) hFh⟩

/-- Convexity for heights with finite domain the integer interval `[l, u]`, through
convexity of the interpolation on the real interval `[l, u]`. This includes the
singleton `l = u` and the empty domain `u < l`. -/
theorem isConvexSeq_iff_convexOn_Icc {l u : ℕ} (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ u) :
    IsConvexSeq h ↔ ConvexOn ℝ (Icc (l : ℝ) u) (linearInterpolate fun n => (h n).untop₀) := by
  rw [isConvexSeq_iff_convexOn_linearInterpolate, interpolationDomain_eq_Icc hdom]

/-- Convexity for heights with finite domain the integer half-line `[l, ∞)`, through
convexity of the interpolation on the real half-line `[l, ∞)`. -/
theorem isConvexSeq_iff_convexOn_Ici {l : ℕ} (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n) :
    IsConvexSeq h ↔ ConvexOn ℝ (Ici (l : ℝ)) (linearInterpolate fun n => (h n).untop₀) := by
  rw [isConvexSeq_iff_convexOn_linearInterpolate, interpolationDomain_eq_Ici hdom]

end TauCeti
