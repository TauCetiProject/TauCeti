/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.CentralShift

/-!
# Distinguished presentations of paths with velocities in a Weyl orbit

A Lakshmibai–Seshadri path of shape `λ` is traversed, on `[0, 1]`, along each of its segments at
a constant velocity lying in the Weyl orbit `W λ`, with different velocities on adjacent segments.
This file shows that such a parametrization is unique, and uses it to make the central shift
`π(t) ↦ π(t) + t χ` well defined on the paths that have one.

For a set `S ⊆ V`, a timed presentation `p` is *distinguished* for `S`
(`TauCeti.PLPath.IsDistinguished S p`) if it has duration `1`, the velocity `d⁻¹ • v` of each of
its segments `(d, v)` lies in `S`, and adjacent segments have different velocities. Suppose that no
two distinct points of `S` lie in the same ray. If `0 ∉ S`, each segment of a distinguished
presentation is a positive multiple of a unique point of `S`, so the presentation is reduced and
both its segments and its durations can be read off the path. If `0 ∈ S`, then `S = {0}` and the
only distinguished presentation is the constant path `[(1, 0)]` of duration `1`. In both cases a
path has at most one distinguished presentation (`TauCeti.PLPath.IsDistinguished.unique`). When
the Weyl group is finite, distinct points of a Weyl orbit never lie in the same ray, so this
applies to `S = W λ` for every weight `λ`, including `λ = 0`
(`RootPairing.pairwise_not_sameRay_orbit_weylGroup`, in
`TauCeti/LinearAlgebra/RootSystem/Weyl/Orbit/Ray.lean`).

Adding the linear path `t ↦ t χ` to a timed presentation (`TauCeti.PLPath.shiftTimed`) is not
well defined on reparametrization classes (`TauCeti.PLPath.not_exists_shiftTimed_on_paths`).
Applied to the distinguished presentation it is: `TauCeti.PLPath.shiftDistinguished S χ π` shifts
the distinguished presentation of `π` for `S`. It sends velocities `u ∈ S` to `u + χ`; for a weight
`χ` fixed by the Weyl group, `w λ + χ = w (λ + χ)`, so it carries paths with velocities in `W λ` to
paths with velocities in `W (λ + χ)` (`RootPairing.mapsTo_add_orbit_weylGroup`). Shifts compose
additively, shifting by `-χ` undoes shifting by `χ`, and a linear form annihilating `χ` sees the
same minimum height.

## Main definitions

* `TauCeti.PLPath.IsDistinguished S p`: `p` is a duration-one timed presentation with velocities
  in `S`, changing velocity at each break.
* `TauCeti.PLPath.HasDistinguished S π`: the path `π` has a distinguished presentation for `S`.
* `TauCeti.PLPath.distinguished S π`: the distinguished presentation of `π`, if it has one.
* `TauCeti.PLPath.shiftDistinguished S χ π`: the path obtained by adding `t ↦ t χ` to the
  distinguished presentation of `π`, or the constant path if `π` has none.

## Main results

* `TauCeti.PLPath.IsDistinguished.isReduced`: if `0 ∉ S`, the segments of a distinguished
  presentation are already reduced.
* `TauCeti.PLPath.IsDistinguished.unique`: **a path has at most one distinguished presentation.**
* `TauCeti.PLPath.IsDistinguished.eq_singleton_of_zero_mem`,
  `TauCeti.PLPath.HasDistinguished.eq_straight_zero`: if `0 ∈ S`, the only distinguished
  presentation is `[(1, 0)]`, and a path with one is the constant path.
* `TauCeti.PLPath.distinguished_ofSegments`: the distinguished presentation of the path presented
  by a distinguished `p` is `p`.
* `TauCeti.PLPath.shiftDistinguished_ofSegments`: the central shift may be computed on any
  distinguished presentation.
* `TauCeti.PLPath.shiftDistinguished_shiftDistinguished`,
  `TauCeti.PLPath.shiftDistinguished_neg_shiftDistinguished`: shifts compose additively and are
  inverted by the opposite shift.
* `TauCeti.PLPath.shiftDistinguished_straight`: the central shift of the straight path along `u`
  is the straight path along `u + χ`.
* `TauCeti.PLPath.endpoint_shiftDistinguished`, `TauCeti.PLPath.minHeight_shiftDistinguished`:
  the endpoint moves by `χ`, and the minimum height for a form annihilating `χ` is unchanged.

## References

* P. Littelmann, *A Littlewood-Richardson rule for symmetrizable Kac-Moody algebras*, Invent.
  Math. 116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.PLPath

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {S T : Set V} {p q : List (𝕜 × V)} {π : PLPath 𝕜 V}

/-! ### Distinguished presentations -/

variable (S p) in
/-- A timed presentation `p` is *distinguished* for a set `S` of velocities if it has duration
`1`, runs along each of its segments `(d, v)` at a constant velocity `d⁻¹ • v` lying in `S`, and
changes velocity at each break. For `S = W λ`, the parametrization of a Lakshmibai–Seshadri path
of shape `λ` by its directions and breaks is distinguished. The converse fails, because no LS chain
condition is imposed. -/
structure IsDistinguished : Prop where
  /-- Every duration is positive. -/
  isTimed : IsTimed p
  /-- The total duration is `1`. -/
  duration_eq_one : duration p = 1
  /-- Every velocity lies in `S`. -/
  slope_mem : ∀ x ∈ p, x.1⁻¹ • x.2 ∈ S
  /-- Adjacent segments have different velocities. -/
  isChain_slope : (p.map fun x ↦ x.1⁻¹ • x.2).IsChain (· ≠ ·)

omit [IsStrictOrderedRing 𝕜] in
theorem IsDistinguished.mono (hp : IsDistinguished S p) (hST : S ⊆ T) : IsDistinguished T p :=
  ⟨hp.isTimed, hp.duration_eq_one, fun x hx ↦ hST (hp.slope_mem x hx), hp.isChain_slope⟩

/-- The straight path along `u ∈ S`, traversed in time `1`, is distinguished for `S`. -/
theorem isDistinguished_singleton {u : V} (hu : u ∈ S) : IsDistinguished S [((1 : 𝕜), u)] :=
  ⟨by simp [isTimed_cons], by simp, by simpa using hu, List.isChain_singleton _⟩

/-- If no two distinct points of `S ∌ 0` lie in the same ray, the segments of a distinguished
presentation for `S` form a reduced segment list: no segment is stationary, and adjacent
segments, being positive multiples of different points of `S`, point in different directions. -/
theorem IsDistinguished.isReduced (hp : IsDistinguished S p)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (h0 : (0 : V) ∉ S) :
    IsReduced 𝕜 (p.map Prod.snd) where
  ne_zero := by
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩ hx0
    exact h0 (by simpa [hx0] using hp.slope_mem x hx)
  isChain := by
    have hchain := hp.isChain_slope
    rw [List.isChain_map] at hchain ⊢
    refine hchain.imp_of_mem_imp fun x y hx hy hxy hsame ↦ hS (hp.slope_mem x hx)
      (hp.slope_mem y hy) hxy ?_
    exact (hsame.pos_smul_left (inv_pos.2 (isTimed_iff.1 hp.isTimed x hx))).pos_smul_right
      (inv_pos.2 (isTimed_iff.1 hp.isTimed y hy))

/-- If `0 ∈ S` and no two distinct points of `S` lie in the same ray, the only distinguished
presentation for `S` is the constant path of duration `1`. -/
theorem IsDistinguished.eq_singleton_of_zero_mem (hp : IsDistinguished S p)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (h0 : (0 : V) ∈ S) : p = [(1, 0)] := by
  -- Every velocity is `0`, since `0` lies in the same ray as every vector.
  have hslope (x : 𝕜 × V) (hx : x ∈ p) : x.1⁻¹ • x.2 = 0 := by
    by_contra hne
    exact hS h0 (hp.slope_mem x hx) (Ne.symm hne) (SameRay.zero_left _)
  have hseg (x : 𝕜 × V) (hx : x ∈ p) : x.2 = 0 := by
    exact (smul_eq_zero.1 (hslope x hx)).resolve_left
      (inv_ne_zero (isTimed_iff.1 hp.isTimed x hx).ne')
  -- So the velocities never change, and there is a single segment, of duration `1`.
  match p, hp, hslope, hseg with
  | [], hp, _, _ => simpa using hp.duration_eq_one
  | [x], hp, _, hseg =>
    have h1 : x.1 = 1 := by simpa using hp.duration_eq_one
    rw [← h1, ← hseg x (List.mem_singleton_self x)]
  | x :: y :: p, hp, hslope, _ =>
    have := hp.isChain_slope
    simp only [List.map_cons, List.isChain_cons_cons] at this
    exact absurd ((hslope x (by simp)).trans (hslope y (by simp)).symm) this.1

/-- **Uniqueness of the distinguished presentation.** If no two distinct points of `S` lie in the
same ray, two distinguished presentations for `S` of the same path are equal. For `S = W λ` this
is the uniqueness of the parametrization of a Lakshmibai–Seshadri path by its directions in `W λ`
and its breaks, including for `λ = 0`, where it is the constant presentation. -/
theorem IsDistinguished.unique (hp : IsDistinguished S p) (hq : IsDistinguished S q)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (h : ofSegments 𝕜 (p.map Prod.snd) = ofSegments 𝕜 (q.map Prod.snd)) : p = q := by
  by_cases h0 : (0 : V) ∈ S
  · rw [hp.eq_singleton_of_zero_mem hS h0, hq.eq_singleton_of_zero_mem hS h0]
  have h' := congrArg PLPath.segments h
  rw [segments_ofSegments, segments_ofSegments, (hp.isReduced hS h0).normalize_eq,
    (hq.isReduced hS h0).normalize_eq] at h'
  exact hS.eq_of_map_snd_eq_of_inv_smul_mem h0
    (fun x hx ↦ ⟨isTimed_iff.1 hp.isTimed x hx, hp.slope_mem x hx⟩)
    (fun x hx ↦ ⟨isTimed_iff.1 hq.isTimed x hx, hq.slope_mem x hx⟩) h'

variable (S π) in
/-- The path `π` has a distinguished presentation for `S`: a duration-one timed presentation with
velocities in `S`, changing velocity at each break. -/
def HasDistinguished : Prop :=
  ∃ p : List (𝕜 × V), IsDistinguished S p ∧ ofSegments 𝕜 (p.map Prod.snd) = π

theorem hasDistinguished_iff :
    HasDistinguished S π ↔ ∃ p : List (𝕜 × V), IsDistinguished S p ∧
      ofSegments 𝕜 (p.map Prod.snd) = π :=
  Iff.rfl

theorem IsDistinguished.hasDistinguished (hp : IsDistinguished S p) :
    HasDistinguished S (ofSegments 𝕜 (p.map Prod.snd)) :=
  ⟨p, hp, rfl⟩

open scoped Classical in
variable (S π) in
/-- The distinguished presentation of `π` for `S`, when `π` has one; it is unique when no two
distinct points of `S` lie in the same ray (`TauCeti.PLPath.distinguished_ofSegments`). The value
`[]` on other paths is a junk value. -/
noncomputable def distinguished : List (𝕜 × V) :=
  if h : HasDistinguished S π then h.choose else []

theorem isDistinguished_distinguished (h : HasDistinguished S π) :
    IsDistinguished S (distinguished S π) := by
  simp only [distinguished, h, ↓reduceDIte]
  exact h.choose_spec.1

@[simp]
theorem ofSegments_distinguished (h : HasDistinguished S π) :
    ofSegments 𝕜 ((distinguished S π).map Prod.snd) = π := by
  simp only [distinguished, h, ↓reduceDIte]
  exact h.choose_spec.2

/-- The distinguished presentation of the path presented by a distinguished presentation `p` is
`p` itself. -/
@[simp]
theorem distinguished_ofSegments (hp : IsDistinguished S p)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) :
    distinguished S (ofSegments 𝕜 (p.map Prod.snd)) = p :=
  (isDistinguished_distinguished hp.hasDistinguished).unique hp hS
    (ofSegments_distinguished hp.hasDistinguished)

/-- If `0 ∈ S` and no two distinct points of `S` lie in the same ray, the distinguished
presentation of a path with one is the constant presentation `[(1, 0)]`. -/
theorem distinguished_of_zero_mem (h : HasDistinguished S π)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (h0 : (0 : V) ∈ S) :
    distinguished S π = [(1, 0)] :=
  (isDistinguished_distinguished h).eq_singleton_of_zero_mem hS h0

/-- If `0 ∈ S` and no two distinct points of `S` lie in the same ray, a path with a distinguished
presentation for `S` is the constant path. For `S = W 0` this is the case `λ = 0`. -/
theorem HasDistinguished.eq_straight_zero (h : HasDistinguished S π)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (h0 : (0 : V) ∈ S) : π = straight 𝕜 0 := by
  rw [← ofSegments_distinguished h, distinguished_of_zero_mem h hS h0, straight_def]
  rfl

/-! ### The central shift -/

omit [IsStrictOrderedRing 𝕜] in
/-- Adding the linear path `t ↦ t χ` to a distinguished presentation for `S` gives a
distinguished presentation for any `T` containing the translates `u + χ` of the velocities
`u ∈ S`. -/
theorem IsDistinguished.shiftTimed (hp : IsDistinguished S p) {χ : V}
    (hST : Set.MapsTo (· + χ) S T) : IsDistinguished T (shiftTimed χ p) := by
  -- The shifted segment `(d, v + d • χ)` has velocity `d⁻¹ • v + χ`.
  have hslope (x : 𝕜 × V) (hx : x ∈ p) : x.1⁻¹ • (x.2 + x.1 • χ) = x.1⁻¹ • x.2 + χ := by
    rw [smul_add, inv_smul_smul₀ (isTimed_iff.1 hp.isTimed x hx).ne']
  refine ⟨(isTimed_shiftTimed_iff χ).2 hp.isTimed, by simpa using hp.duration_eq_one, ?_, ?_⟩
  · simp only [shiftTimed_def, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    rw [hslope x hx]
    exact hST (hp.slope_mem x hx)
  · have := hp.isChain_slope
    rw [List.isChain_map] at this
    rw [shiftTimed_def, List.map_map, List.isChain_map]
    exact this.imp_of_mem_imp fun x y hx hy hxy ↦ by
      simpa [hslope x hx, hslope y hy] using hxy

variable (S) in
/-- The *central shift* of `π` by `χ`: the path obtained by adding the linear path `t ↦ t χ` to
the distinguished presentation of `π` for `S`. When `π` has velocities in a Weyl orbit `W λ` and
`χ` is fixed by the Weyl group, this is the transport of `π` to a path with velocities in
`W (λ + χ)`. Adding `t ↦ t χ` to an arbitrary presentation of `π` is not well defined
(`TauCeti.PLPath.not_exists_shiftTimed_on_paths`). If `π` has no distinguished presentation for
`S`, then `distinguished S π = []` and the value is the constant junk path `ofSegments 𝕜 []`. -/
noncomputable def shiftDistinguished (χ : V) (π : PLPath 𝕜 V) : PLPath 𝕜 V :=
  ofSegments 𝕜 ((shiftTimed χ (distinguished S π)).map Prod.snd)

/-- **The central shift is well defined.** If no two distinct points of `S` lie in the same ray,
the central shift of the path presented by a distinguished presentation `p` is computed by adding
`t ↦ t χ` to `p`. -/
theorem shiftDistinguished_ofSegments (hp : IsDistinguished S p)
    (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (χ : V) :
    shiftDistinguished S χ (ofSegments 𝕜 (p.map Prod.snd)) =
      ofSegments 𝕜 ((shiftTimed χ p).map Prod.snd) := by
  rw [shiftDistinguished, distinguished_ofSegments hp hS]

/-- The central shift by `χ` sends a path with a distinguished presentation for `S` to a path
with a distinguished presentation for any `T` containing the translates `u + χ`, `u ∈ S`. -/
theorem HasDistinguished.shiftDistinguished (h : HasDistinguished S π) {χ : V}
    (hST : Set.MapsTo (· + χ) S T) : HasDistinguished T (shiftDistinguished S χ π) :=
  ((isDistinguished_distinguished h).shiftTimed hST).hasDistinguished

@[simp]
theorem shiftDistinguished_zero (h : HasDistinguished S π) : shiftDistinguished S 0 π = π := by
  rw [shiftDistinguished, shiftTimed_zero, ofSegments_distinguished h]

/-- **Central shifts compose additively.** Shifting by `χ`, from velocities in `S` to velocities
in `T`, and then by `ψ` is the same as shifting by `χ + ψ`. -/
theorem shiftDistinguished_shiftDistinguished (h : HasDistinguished S π) {χ : V}
    (hST : Set.MapsTo (· + χ) S T) (hT : T.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) (ψ : V) :
    shiftDistinguished T ψ (shiftDistinguished S χ π) = shiftDistinguished S (χ + ψ) π := by
  calc shiftDistinguished T ψ (shiftDistinguished S χ π)
      = ofSegments 𝕜 ((shiftTimed ψ (shiftTimed χ (distinguished S π))).map Prod.snd) :=
        shiftDistinguished_ofSegments ((isDistinguished_distinguished h).shiftTimed hST) hT ψ
    _ = shiftDistinguished S (χ + ψ) π := by rw [shiftTimed_shiftTimed, shiftDistinguished]

/-- **The inverse of a central shift.** Shifting by `-χ` undoes shifting by `χ`. -/
theorem shiftDistinguished_neg_shiftDistinguished (h : HasDistinguished S π) {χ : V}
    (hST : Set.MapsTo (· + χ) S T) (hT : T.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) :
    shiftDistinguished T (-χ) (shiftDistinguished S χ π) = π := by
  rw [shiftDistinguished_shiftDistinguished h hST hT, add_neg_cancel, shiftDistinguished_zero h]

/-- The central shift by `χ` of the straight path along `u ∈ S` is the straight path along
`u + χ`. For `S = W λ` and `u = λ` this sends the straight path of shape `λ` to the straight path
of shape `λ + χ`; for `λ = 0` it sends the constant path to the straight path along `χ`. -/
theorem shiftDistinguished_straight (hS : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) {u : V}
    (hu : u ∈ S) (χ : V) : shiftDistinguished S χ (straight 𝕜 u) = straight 𝕜 (u + χ) := by
  have h := shiftDistinguished_ofSegments (isDistinguished_singleton (𝕜 := 𝕜) hu) hS χ
  simpa [shiftTimed_cons, ← straight_def] using h

/-- The central shift by `χ` moves the endpoint by `χ`, since the distinguished presentation has
duration `1`. -/
@[simp]
theorem endpoint_shiftDistinguished (h : HasDistinguished S π) (χ : V) :
    (shiftDistinguished S χ π).endpoint = π.endpoint + χ := by
  rw [shiftDistinguished, endpoint_ofSegments_shiftTimed, ofSegments_distinguished h,
    (isDistinguished_distinguished h).duration_eq_one, one_smul]

/-- A linear form annihilating `χ` has the same minimum height on `π` and on its central shift by
`χ`. In a weight space this applies to every simple coroot when `χ` is a central weight. -/
@[simp]
theorem minHeight_shiftDistinguished {f : Module.Dual 𝕜 V} {χ : V} (hχ : f χ = 0)
    (h : HasDistinguished S π) : (shiftDistinguished S χ π).minHeight f = π.minHeight f := by
  rw [shiftDistinguished, minHeight_ofSegments_shiftTimed hχ, ofSegments_distinguished h]

end TauCeti.PLPath
