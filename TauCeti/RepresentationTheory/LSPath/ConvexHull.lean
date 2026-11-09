/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Barycenter
public import TauCeti.RepresentationTheory.LSPath.Reparametrization
import Mathlib.Tactic.Linarith

/-!
# Paths with slopes in a set stay in its scaled convex hull

A Lakshmibai–Seshadri path `π` of shape `λ` has a distinguished parametrization, on `[0, 1]`,
which runs along each of its segments at a constant velocity lying in the Weyl orbit `W λ`. So
`π(t)` is the sum of the elapsed durations of its segments times weights of `W λ`, with total
duration `t`, and `π(t) / t` is a convex combination of points of `W λ`:

`π(t) ∈ t · Conv(W λ)` for `0 < t ≤ 1`, and `π(0) = 0`.

This file proves that convexity statement for an arbitrary timed presentation
(`TauCeti.PLPath.evalTimed`) whose velocities `d⁻¹ • v` lie in a set `S`, of any positive
duration. When `0 ∈ Conv(S)` the scaled hull `t · Conv(S)` lies in `Conv(S)` for `0 ≤ t ≤ 1`, and
the path stays in `Conv(S)` itself. For a root system with a finite Weyl group, `0` lies in the
convex hull of every Weyl orbit (`RootPairing.zero_mem_convexHull_orbit_weylGroup`), so a path
with velocities in `W λ` stays in `Conv(W λ)` up to time `1`.

Only the scaled statement holds without that premise. For a weight `λ ≠ 0` fixed by the Weyl
group, as for a nonzero central weight of a reductive group, `W λ = {λ}`, the straight path is
`π(t) = t λ`, and `π(t) ∉ Conv(W λ)` for `t < 1`.

These statements concern parametrized representatives. Another timed presentation of the same
`TauCeti.PLPath` need not have velocities in `S`.

## Main results

* `TauCeti.PLPath.evalTimed_mem_smul_convexHull`: **a path with velocities in `S` lies in
  `t · Conv(S)` at each time `0 < t` up to its duration.**
* `TauCeti.PLPath.inv_smul_evalTimed_mem_convexHull`: equivalently, `π(t) / t ∈ Conv(S)`.
* `TauCeti.PLPath.endpoint_ofSegments_mem_smul_convexHull`: the endpoint of a path of duration
  `D > 0` with velocities in `S` lies in `D • Conv(S)`.
* `TauCeti.PLPath.evalTimed_mem_convexHull`: if `0 ∈ Conv(S)`, the path lies in `Conv(S)` for
  `0 ≤ t ≤ 1`.
* `TauCeti.PLPath.evalTimed_mem_convexHull_orbit_weylGroup`: for a root system with a finite Weyl
  group, a path with velocities in a Weyl orbit `W λ` lies in `Conv(W λ)` for `0 ≤ t ≤ 1`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, §4.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace PLPath

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {p : List (𝕜 × V)} {S : Set V} {t : 𝕜}

/-- **Convexity of paths with prescribed velocities.** If a timed presentation runs along each
segment `v` of duration `d` at a velocity `d⁻¹ • v` lying in `S`, then at each time `0 < t` up to
its total duration its parametrized path lies in the scaled convex hull `t • Conv(S)`. -/
theorem evalTimed_mem_smul_convexHull (hp : IsTimed p) (hS : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ S)
    (ht : 0 < t) (htd : t ≤ duration p) : evalTimed p t ∈ t • convexHull 𝕜 S := by
  induction p generalizing t with
  | nil => exact absurd (htd.trans_eq duration_nil) ht.not_ge
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    rw [isTimed_cons] at hp
    rw [List.forall_mem_cons] at hS
    rw [duration_cons] at htd
    -- The first segment is `d • s` for its velocity `s ∈ S`.
    have hs : d⁻¹ • v ∈ convexHull 𝕜 S := subset_convexHull 𝕜 S hS.1
    rcases le_or_gt t d with htd' | hdt
    · -- At time `t ≤ d` the path is `t • s`.
      rw [evalTimed_cons, min_eq_left htd', max_eq_right ht.le,
        evalTimed_of_nonpos hp.2.nonneg (sub_nonpos.2 htd'), add_zero, div_eq_mul_inv, mul_smul]
      exact Set.smul_mem_smul_set hs
    · -- At time `t > d` the path is `d • s + (t - d) • c` for some `c ∈ Conv(S)`, by induction.
      obtain ⟨c, hc, hce⟩ := Set.mem_smul_set.1 (ih hp.2 hS.2 (sub_pos.2 hdt) (by linarith))
      rw [evalTimed_cons_of_le hp.1 hdt.le, ← hce]
      refine Set.mem_smul_set.2 ⟨(d / t) • d⁻¹ • v + ((t - d) / t) • c,
        convex_convexHull 𝕜 S hs hc (div_nonneg hp.1.le ht.le)
          (div_nonneg (sub_nonneg.2 hdt.le) ht.le) (by field_simp; ring), ?_⟩
      have := hp.1.ne'
      have := ht.ne'
      match_scalars <;> field_simp

/-- **Convexity of paths with prescribed velocities**, in the form `π(t) / t ∈ Conv(S)` for
`0 < t` up to the total duration. -/
theorem inv_smul_evalTimed_mem_convexHull (hp : IsTimed p) (hS : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ S)
    (ht : 0 < t) (htd : t ≤ duration p) : t⁻¹ • evalTimed p t ∈ convexHull 𝕜 S :=
  (Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne' _ _).1 (evalTimed_mem_smul_convexHull hp hS ht htd)

/-- The endpoint of a path of positive duration `D` with velocities in `S` lies in `D • Conv(S)`.
For the distinguished parametrization of a Lakshmibai–Seshadri path of shape `λ`, on `[0, 1]`,
this says that its weight lies in `Conv(W λ)`. -/
theorem endpoint_ofSegments_mem_smul_convexHull (hp : IsTimed p)
    (hS : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ S) (hd : 0 < duration p) :
    (ofSegments 𝕜 (p.map Prod.snd)).endpoint ∈ duration p • convexHull 𝕜 S :=
  evalTimed_duration hp ▸ evalTimed_mem_smul_convexHull hp hS hd le_rfl

/-- If `0 ∈ Conv(S)`, a path with velocities in `S` lies in `Conv(S)` at every time
`0 ≤ t ≤ 1`, whatever its total duration. -/
theorem evalTimed_mem_convexHull (hp : IsTimed p) (hS : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ S)
    (h₀ : (0 : V) ∈ convexHull 𝕜 S) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    evalTimed p t ∈ convexHull 𝕜 S := by
  -- After its total duration the path stays at its value at that time.
  obtain ⟨u, hu₀, hu₁, hu⟩ :
      ∃ u, 0 ≤ u ∧ u ≤ 1 ∧ u ≤ duration p ∧ evalTimed p t = evalTimed p u := by
    rcases le_total t (duration p) with htd | hdt
    · exact ⟨t, ht₀, ht₁, htd, rfl⟩
    · refine ⟨duration p, duration_nonneg hp.nonneg, hdt.trans ht₁, le_rfl, ?_⟩
      rw [evalTimed_of_duration_le hp hdt, evalTimed_of_duration_le hp le_rfl]
  rw [hu.2]
  rcases hu₀.eq_or_lt with rfl | hu₀
  · rwa [evalTimed_zero hp.nonneg]
  obtain ⟨c, hc, hce⟩ := Set.mem_smul_set.1 (evalTimed_mem_smul_convexHull hp hS hu₀ hu.1)
  rw [← hce]
  exact (convex_convexHull 𝕜 S).smul_mem_of_zero_mem h₀ hc ⟨hu₀.le, hu₁⟩

/-- **Paths with velocities in a Weyl orbit stay in its convex hull.** For a root system with a
finite Weyl group over a linearly ordered field, a path whose velocities lie in the Weyl orbit
`W λ` lies in `Conv(W λ)` at every time `0 ≤ t ≤ 1`. -/
theorem evalTimed_mem_convexHull_orbit_weylGroup {ι N : Type*} [AddCommGroup N] [Module 𝕜 N]
    (P : RootPairing ι 𝕜 V N) [P.IsRootSystem] [Finite P.weylGroup] {lam : V} (hp : IsTimed p)
    (hS : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ MulAction.orbit P.weylGroup lam) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    evalTimed p t ∈ convexHull 𝕜 (MulAction.orbit P.weylGroup lam) :=
  evalTimed_mem_convexHull hp hS (P.zero_mem_convexHull_orbit_weylGroup lam) ht₀ ht₁

end PLPath

end TauCeti
