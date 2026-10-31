/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond
public import TauCeti.RepresentationTheory.LSPath.Reparametrization

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.List
import TauCeti.Data.Rat.BoundedDen

/-!
# Lakshmibai–Seshadri paths

Let `λ` be a weight of a finite reduced root datum with a base. Littelmann encodes a
**Lakshmibai–Seshadri path** of shape `λ` by a pair `π = (τ; a)` of

* a strictly decreasing sequence `τ₀ > τ₁ > ⋯ > τ_l` of cosets in the parabolic quotient
  `W / W_λ`, modelled by their minimal coset representatives; and
* a sequence of rational times `0 = a₀ < a₁ < ⋯ < a_{l+1} = 1`,

such that for each internal break `a_{j+1}` there is an `a_{j+1}`-chain for `(τ_j, τ_{j+1})`: a
saturated chain of `W / W_λ` from `τ_j` down to `τ_{j+1}` along which `a_{j+1}` times every bond
`b_λ(x, y)` is an integer (`TauCeti.IsAChain`). The path it encodes has constant velocity the
orbit weight `τ_j λ` during `[a_j, a_{j+1}]`:

`π(t) = ∑_{k < j} (a_{k+1} - a_k) τ_k λ + (t - a_j) τ_j λ` for `a_j ≤ t ≤ a_{j+1}`.

This file defines these encodings as the structure `TauCeti.LSPath`, together with their
distinguished timed presentation, whose velocities are the orbit weights `τ_j λ`, and the
piecewise-linear path `TauCeti.LSPath.toPLPath` they present. The weights live in a `ℤ`-module
`M`, so that bonds are integers; the paths live in a vector space `V` over an ordered field,
reached by an additive map `f : M →+ V` (typically `M → ℚ ⊗ M`).

The main result is finiteness: for dominant `λ` there are only finitely many
Lakshmibai–Seshadri paths of shape `λ`. The Weyl group is finite, so there are finitely many
cosets, and a strictly decreasing sequence of them is no longer than their number. The
denominator of an internal break divides the bond gcd of its chain, which is positive and divides
a bond, and the bonds `b_λ(x, y)` take finitely many values. So the breaks have bounded
denominators in `(0, 1)`.

The straight path `t ↦ t λ` (`TauCeti.LSPath.straight`) and, for a simple root `αᵢ` with
`⟨λ, αᵢ^∨⟩ ≠ 0`, the paths `(sᵢ, 1; 0, a, 1)` with `a ⟨λ, αᵢ^∨⟩ ∈ ℤ`
(`TauCeti.LSPath.simple`) are Lakshmibai–Seshadri paths.

## Main definitions

* `TauCeti.LSPath`: Littelmann's encoding `(τ; a)` of a Lakshmibai–Seshadri path of shape `λ`.
* `TauCeti.LSPath.duration`: the duration `a_{j+1} - a_j` of the `j`-th segment.
* `TauCeti.LSPath.timed`: the distinguished timed presentation, running with constant velocity
  `τ_j λ` for time `a_{j+1} - a_j`.
* `TauCeti.LSPath.toPLPath`: the piecewise-linear path presented by it.
* `TauCeti.LSPath.straight` and `TauCeti.LSPath.simple`: the straight path and the
  two-direction paths along a simple root.

## Main results

* `TauCeti.LSPath.finite`: **for dominant `λ` there are finitely many Lakshmibai–Seshadri paths
  of shape `λ`.**
* `TauCeti.LSPath.bruhatLE_dir_succ` and `TauCeti.LSPath.strictAnti_length_dir`: the directions
  strictly decrease in the Bruhat order, and so do their lengths.
* `TauCeti.LSPath.sum_duration`, `TauCeti.LSPath.isTimed_timed` and
  `TauCeti.LSPath.duration_timed`: the distinguished presentation is a timed presentation of
  duration `1`.
* `TauCeti.LSPath.inv_smul_mem_range_of_mem_timed`: its velocities lie in the Weyl orbit of `λ`.
* `TauCeti.LSPath.endpoint_toPLPath`: the endpoint is `∑_j (a_{j+1} - a_j) τ_j λ`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

universe u w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

variable (P b) in
/-- A **Lakshmibai–Seshadri path** of shape `λ`, in Littelmann's encoding `(τ₀, …, τ_l; a₀, …,
a_{l+1})`: minimal coset representatives `τ₀ > τ₁ > ⋯ > τ_l` of `W / W_λ` (the directions) and
rational times `0 = a₀ < a₁ < ⋯ < a_{l+1} = 1`, such that for each internal break `a_{j+1}` some
saturated chain of `W / W_λ` from `τ_j` down to `τ_{j+1}` is an `a_{j+1}`-chain. The path runs
along the orbit weight `τ_j λ` during `[a_j, a_{j+1}]` (`TauCeti.LSPath.toPLPath`). The
definition makes sense for every weight `λ`; Littelmann's theory, and the finiteness theorem
`TauCeti.LSPath.finite`, concern dominant `λ`. -/
structure LSPath (lam : M) where
  /-- The number `l` of internal breaks; there are `l + 1` directions. -/
  length : ℕ
  /-- The directions `τ₀, …, τ_l`, as minimal coset representatives of `W / W_λ`. -/
  dir : Fin (length + 1) →
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}
  /-- The times `a₀, …, a_{l+1}` at which the path changes direction, including the ends. -/
  time : Fin (length + 2) → ℚ
  /-- The path starts at time `a₀ = 0`. -/
  time_zero : time 0 = 0
  /-- The path ends at time `a_{l+1} = 1`. -/
  time_last : time (Fin.last _) = 1
  /-- The times strictly increase. -/
  strictMono_time : StrictMono time
  /-- Consecutive directions are distinct. -/
  dir_succ_ne (j : Fin length) : dir j.succ ≠ dir j.castSucc
  /-- Each internal break `a_{j+1}` admits an `a_{j+1}`-chain from `τ_j` down to `τ_{j+1}`. -/
  exists_isAChain (j : Fin length) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head = dir j.castSucc ∧ C.last = dir j.succ ∧ IsAChain (time j.castSucc.succ) lam C

namespace LSPath

variable {lam : M} (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

/-- A Lakshmibai–Seshadri path is determined by its lists of directions and of times. -/
@[ext]
theorem ext {π π' : LSPath P b lam} (hdir : List.ofFn π.dir = List.ofFn π'.dir)
    (htime : List.ofFn π.time = List.ofFn π'.time) : π = π' := by
  obtain ⟨l, τ, a, _, _, _, _, _⟩ := π
  obtain ⟨l', τ', a', _, _, _, _, _⟩ := π'
  obtain rfl : l = l' := by simpa using congrArg List.length hdir
  obtain rfl := List.ofFn_injective hdir
  obtain rfl := List.ofFn_injective htime
  rfl

/-- The directions of a Lakshmibai–Seshadri path decrease in the Bruhat order of `W / W_λ`; they
strictly decrease by `TauCeti.LSPath.dir_succ_ne`. -/
theorem bruhatLE_dir_succ (π : LSPath P b lam) (j : Fin π.length) :
    (weylCoxeterSystem P b).BruhatLE (π.dir j.succ) (π.dir j.castSucc) := by
  obtain ⟨C, hhead, hlast, -⟩ := π.exists_isAChain j
  exact hhead ▸ hlast ▸ C.bruhatLE_last_head

/-- The Coxeter lengths of the directions of a Lakshmibai–Seshadri path strictly decrease. -/
theorem strictAnti_length_dir (π : LSPath P b lam) :
    StrictAnti fun j ↦ (weylCoxeterSystem P b).length (π.dir j) :=
  Fin.strictAnti_iff_succ_lt.mpr fun j ↦
    (π.bruhatLE_dir_succ j).length_lt_of_ne fun h ↦ π.dir_succ_ne j (Subtype.ext h)

/-- The directions of a Lakshmibai–Seshadri path are pairwise distinct. -/
theorem dir_injective (π : LSPath P b lam) : Function.Injective π.dir :=
  fun _ _ h ↦
    π.strictAnti_length_dir.injective (congrArg (fun x ↦ (weylCoxeterSystem P b).length x.1) h)

/-- The duration `a_{j+1} - a_j` of the `j`-th segment of a Lakshmibai–Seshadri path, during which
it runs along the orbit weight `τ_j λ`. -/
def duration (π : LSPath P b lam) (j : Fin (π.length + 1)) : ℚ :=
  π.time j.succ - π.time j.castSucc

theorem duration_def (π : LSPath P b lam) (j : Fin (π.length + 1)) :
    π.duration j = π.time j.succ - π.time j.castSucc :=
  (rfl)

/-- The segments of a Lakshmibai–Seshadri path have positive duration. -/
theorem duration_pos (π : LSPath P b lam) (j : Fin (π.length + 1)) : 0 < π.duration j :=
  sub_pos.mpr (π.strictMono_time j.castSucc_lt_succ)

/-- The durations of the segments of a Lakshmibai–Seshadri path add up to `1`. -/
@[simp]
theorem sum_duration (π : LSPath P b lam) : ∑ j, π.duration j = 1 := by
  rw [← Finset.Iic_top, Fin.top_eq_last]
  simp only [duration]
  rw [Fin.sum_Iic_sub, Fin.succ_last, π.time_last, π.time_zero, sub_zero]

/-- The **distinguished timed presentation** of a Lakshmibai–Seshadri path: for each direction
`τ_j`, the segment `(a_{j+1} - a_j) τ_j λ` traversed during time `a_{j+1} - a_j`, so with constant
velocity `f (τ_j λ)`, carried to `V` by `f`. -/
noncomputable def timed (π : LSPath P b lam) : List (𝕜 × V) :=
  List.ofFn fun j ↦ ((π.duration j : 𝕜), (π.duration j : 𝕜) • f ((π.dir j).1 • lam))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem timed_def (π : LSPath P b lam) :
    π.timed 𝕜 f =
      List.ofFn fun j ↦ ((π.duration j : 𝕜), (π.duration j : 𝕜) • f ((π.dir j).1 • lam)) :=
  (rfl)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The segments of the distinguished timed presentation are the segments `(a_{j+1} - a_j) τ_j λ`,
traversed during time `a_{j+1} - a_j`. -/
theorem mem_timed_iff (π : LSPath P b lam) {y : 𝕜 × V} :
    y ∈ π.timed 𝕜 f ↔
      ∃ j, ((π.duration j : 𝕜), (π.duration j : 𝕜) • f ((π.dir j).1 • lam)) = y := by
  rw [timed_def, List.mem_ofFn]

/-- Every segment of the distinguished timed presentation of a Lakshmibai–Seshadri path has
strictly positive duration. -/
theorem isTimed_timed (π : LSPath P b lam) : PLPath.IsTimed (π.timed 𝕜 f) := by
  simp only [PLPath.isTimed_iff, timed, List.forall_mem_ofFn_iff, Rat.cast_pos]
  exact π.duration_pos

/-- The distinguished timed presentation of a Lakshmibai–Seshadri path has duration `1`. -/
@[simp]
theorem duration_timed (π : LSPath P b lam) : PLPath.duration (π.timed 𝕜 f) = 1 := by
  simp only [PLPath.duration_def, timed, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [← Rat.cast_sum, sum_duration, Rat.cast_one]

/-- The velocities of the distinguished timed presentation of a Lakshmibai–Seshadri path of shape
`λ` lie in the Weyl orbit of `λ`, carried to `V` by `f`. -/
theorem inv_smul_mem_range_of_mem_timed (π : LSPath P b lam) {y : 𝕜 × V}
    (hy : y ∈ π.timed 𝕜 f) : y.1⁻¹ • y.2 ∈ Set.range fun w : P.weylGroup ↦ f (w • lam) := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  exact ⟨π.dir j, (inv_smul_smul₀ (Rat.cast_ne_zero.mpr (π.duration_pos j).ne') _).symm⟩

/-- The piecewise-linear path of a Lakshmibai–Seshadri path, presented by its distinguished timed
presentation and carried to `V` by `f`. -/
noncomputable def toPLPath (π : LSPath P b lam) : PLPath 𝕜 V :=
  PLPath.ofSegments 𝕜 ((π.timed 𝕜 f).map Prod.snd)

theorem toPLPath_def (π : LSPath P b lam) :
    π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜 ((π.timed 𝕜 f).map Prod.snd) :=
  (rfl)

/-- The endpoint of a Lakshmibai–Seshadri path is `∑_j (a_{j+1} - a_j) τ_j λ`. -/
theorem endpoint_toPLPath (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).endpoint = ∑ j, (π.duration j : 𝕜) • f ((π.dir j).1 • lam) := by
  simp only [toPLPath, PLPath.endpoint_ofSegments, timed, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]

section Examples

variable (lam) in
/-- The **straight** Lakshmibai–Seshadri path `t ↦ t λ`, with the single direction `1`. -/
noncomputable def straight : LSPath P b lam where
  length := 0
  dir _ := ⟨1, (weylCoxeterSystem P b).isMinimalCosetRep_one _⟩
  time := ![0, 1]
  time_zero := rfl
  time_last := rfl
  strictMono_time := Fin.strictMono_iff_lt_succ.mpr fun j ↦ by
    fin_cases j
    simp
  dir_succ_ne j := j.elim0
  exists_isAChain j := j.elim0

@[simp]
theorem length_straight : (straight lam : LSPath P b lam).length = 0 :=
  (rfl)

@[simp]
theorem dir_straight (j : Fin ((straight lam : LSPath P b lam).length + 1)) :
    ((straight lam : LSPath P b lam).dir j).1 = 1 :=
  (rfl)

/-- The straight Lakshmibai–Seshadri path has the single segment from time `0` to time `1`. -/
@[simp]
theorem time_straight (k : Fin ((straight lam : LSPath P b lam).length + 2)) :
    (straight lam : LSPath P b lam).time k = k.val := by
  fin_cases k <;> rfl

/-- The path of the straight Lakshmibai–Seshadri path is the straight path along `λ`. -/
@[simp]
theorem toPLPath_straight :
    (straight lam : LSPath P b lam).toPLPath 𝕜 f = PLPath.straight 𝕜 (f lam) := by
  simp [toPLPath, timed, duration, straight, PLPath.straight_def]

/-- The **two-direction** Lakshmibai–Seshadri path `(sᵢ, 1; 0, a, 1)` along a simple root `αᵢ`
with `⟨λ, αᵢ^∨⟩ ≠ 0`, for `0 < a < 1` with `a ⟨λ, αᵢ^∨⟩ ∈ ℤ`. It runs along `sᵢ λ` until time
`a`, then along `λ`. The chain `sᵢ ⋗ 1` has the single bond `⟨λ, αᵢ^∨⟩`. -/
noncomputable def simple (i : b.support) (hi : P.coroot' i lam ≠ 0) (a : ℚ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (ha : ∃ z : ℤ, a * P.coroot' i lam = z) : LSPath P b lam where
  length := 1
  dir := ![⟨(weylCoxeterSystem P b).simple i,
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi).isMinimalCosetRep_right⟩,
    ⟨1, (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi).isMinimalCosetRep_left⟩]
  time := ![0, a, 1]
  time_zero := rfl
  time_last := rfl
  strictMono_time := Fin.strictMono_iff_lt_succ.mpr fun j ↦ by
    fin_cases j
    · simpa using ha₀
    · simpa using ha₁
  dir_succ_ne j := by
    fin_cases j
    simpa [Subtype.ext_iff, eq_comm] using
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi).ne
  exists_isAChain j := by
    fin_cases j
    -- The chain `sᵢ ⋗ 1` has the single bond `⟨λ, αᵢ^∨⟩`.
    have h := minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero (b := b) hi
    refine ⟨(RelSeries.singleton _ ⟨_, h.isMinimalCosetRep_right⟩ :
      (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)).snoc
      ⟨1, h.isMinimalCosetRep_left⟩ h, by simp, by simp, ?_⟩
    refine (isAChain_snoc_iff h).mpr ⟨isAChain_singleton _, ?_⟩
    rw [RelSeries.last_singleton, reflectionBond_simple_smul_one_smul i]
    simpa using ha

section Simple

variable {i : b.support} {hi : P.coroot' i lam ≠ 0} {a : ℚ} {ha₀ : 0 < a} {ha₁ : a < 1}
  {ha : ∃ z : ℤ, a * P.coroot' i lam = z}

@[simp]
theorem length_simple : (simple i hi a ha₀ ha₁ ha).length = 1 :=
  (rfl)

/-- The two-direction Lakshmibai–Seshadri path `(sᵢ, 1; 0, a, 1)` first runs along `sᵢ λ`. -/
@[simp]
theorem dir_simple_zero : ((simple i hi a ha₀ ha₁ ha).dir 0).1 = (weylCoxeterSystem P b).simple i :=
  (rfl)

/-- The two-direction Lakshmibai–Seshadri path `(sᵢ, 1; 0, a, 1)` then runs along `λ`. -/
@[simp]
theorem dir_simple_one : ((simple i hi a ha₀ ha₁ ha).dir 1).1 = 1 :=
  (rfl)

/-- The two-direction Lakshmibai–Seshadri path `(sᵢ, 1; 0, a, 1)` changes direction at time `a`. -/
@[simp]
theorem time_simple_one : (simple i hi a ha₀ ha₁ ha).time 1 = a :=
  (rfl)

end Simple

/-- The path of the two-direction Lakshmibai–Seshadri path `(sᵢ, 1; 0, a, 1)` runs along `sᵢ λ`
for time `a`, then along `λ`. -/
theorem toPLPath_simple (i : b.support) (hi : P.coroot' i lam ≠ 0) (a : ℚ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (ha : ∃ z : ℤ, a * P.coroot' i lam = z) :
    (simple i hi a ha₀ ha₁ ha).toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      [(a : 𝕜) • f ((weylCoxeterSystem P b).simple i • lam), ((1 - a : ℚ) : 𝕜) • f lam] := by
  simp [toPLPath, timed, duration, simple, List.ofFn_succ]

end Examples

section Finite

variable [P.flip.IsReduced]

/-- The bond gcd of the chain witnessing an internal break of a Lakshmibai–Seshadri path is a
positive multiple of the denominator of the break, and divides a bond `b_λ(x, y)`. -/
private theorem exists_den_le_natAbs_reflectionBond (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) (j : Fin π.length) :
    ∃ x y : P.weylGroup,
      (π.time j.castSucc.succ).den ≤ (P.reflectionBond b (x • lam) (y • lam)).natAbs := by
  obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
  -- The chain is nonempty, since its ends are distinct directions.
  have hlen : C.length ≠ 0 := fun h ↦ π.dir_succ_ne j <| by
    rw [← hhead, ← hlast]
    exact C.subsingleton_of_length_eq_zero h C.last_mem C.head_mem
  have hpos : 0 < bondGcd lam C :=
    Nat.pos_of_ne_zero ((bondGcd_eq_zero_iff hlam).not.mpr hlen)
  refine ⟨_, _, (Nat.le_of_dvd hpos (isAChain_iff_den_dvd_bondGcd.mp hC)).trans
    (Nat.le_of_dvd ?_ (bondGcd_dvd ⟨0, Nat.pos_of_ne_zero hlen⟩))⟩
  exact Int.natAbs_pos.mpr (reflectionBond_pos_of_minimalCosetRepCovBy hlam
    (C.minimalCosetRepCovBy ⟨0, Nat.pos_of_ne_zero hlen⟩)).ne'

/-- **There are finitely many Lakshmibai–Seshadri paths of a dominant shape `λ`.** The
directions strictly decrease in the finite parabolic quotient `W / W_λ`, and the times are
rationals in `[0, 1]` whose denominators are bounded by the bonds `b_λ(x, y)`. -/
theorem finite (hlam : lam ∈ dominantChamber P b) : Finite (LSPath P b lam) := by
  have := P.finite_weylGroup_of_base b
  -- The bonds `b_λ(x, y)` take finitely many values, so they are bounded by some `B`.
  obtain ⟨B, hB⟩ := (Set.finite_range fun xy : P.weylGroup × P.weylGroup ↦
    (P.reflectionBond b (xy.1 • lam) (xy.2 • lam)).natAbs).bddAbove
  -- The times lie in the finite set `S` of rationals in `[0, 1]` with denominator at most
  -- `B + 1`; the end times have denominator `1`.
  set S : Set ℚ := {q | q.den ≤ B + 1 ∧ (q : ℝ) ∈ Set.Icc 0 1}
  have hS : S.Finite := Metric.isBounded_Icc (0 : ℝ) 1 |>.finite_setOf_rat_den_le (B + 1)
  have hmem (π : LSPath P b lam) (k : Fin (π.length + 2)) : π.time k ∈ S := by
    have h₀ : 0 ≤ π.time k := π.time_zero ▸ π.strictMono_time.monotone (Fin.zero_le k)
    have h₁ : π.time k ≤ 1 := π.time_last ▸ π.strictMono_time.monotone (Fin.le_last k)
    refine ⟨?_, by exact_mod_cast h₀, by exact_mod_cast h₁⟩
    -- The end times are integers; each internal time is the break of a chain.
    induction k using Fin.lastCases with
    | last => simp [π.time_last]
    | cast k =>
      induction k using Fin.cases with
      | zero => simp [π.time_zero]
      | succ j =>
        obtain ⟨x, y, hxy⟩ := exists_den_le_natAbs_reflectionBond hlam π j
        exact (Fin.succ_castSucc j ▸ hxy).trans ((hB ⟨(x, y), rfl⟩).trans (Nat.le_succ B))
  have := hS.to_subtype
  -- Encode a path by its lists of directions and times, of bounded length.
  set R := {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}
  have hcard (π : LSPath P b lam) : π.length + 2 ≤ Nat.card R + 1 := by
    have := Nat.card_le_card_of_injective (β := R) π.dir π.dir_injective
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  let e (π : LSPath P b lam) : {l : List R // l.length ≤ Nat.card R + 1} ×
      {l : List S // l.length ≤ Nat.card R + 1} :=
    (⟨List.ofFn π.dir, by simpa using (hcard π).trans' (Nat.le_succ _)⟩,
      ⟨List.ofFn fun k ↦ ⟨π.time k, hmem π k⟩, by simpa using hcard π⟩)
  have := (List.finite_length_le R (Nat.card R + 1)).to_subtype
  have := (List.finite_length_le S (Nat.card R + 1)).to_subtype
  refine Finite.of_injective e fun π π' h ↦ ext ?_ ?_
  · exact congrArg Subtype.val (Prod.ext_iff.mp h).1
  · have := congrArg (List.map Subtype.val ∘ Subtype.val) (Prod.ext_iff.mp h).2
    simpa [e, List.map_ofFn, Function.comp_def] using this

end Finite

end LSPath

end TauCeti
