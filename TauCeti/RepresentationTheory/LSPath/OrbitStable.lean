/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
public import TauCeti.RepresentationTheory.LSPath.Distinguished

/-!
# Root operators preserve velocities in a Weyl orbit

A Lakshmibai–Seshadri path of shape `λ` runs along each of its segments at a constant velocity in
the Weyl orbit `W λ`. Littelmann's lowering operator `f_α` reflects some pieces of a path by
`s_α` and translates the rest, so it changes velocities only by `s_α`. Since `W λ` is stable under
`s_α`, the lowered path again runs at velocities in `W λ`, with the same total time. This file
proves that statement, for the raising operator `e_α` as well, and for an arbitrary set `S` of
velocities stable under the reflection `Module.preReflection x f`. This is the velocity half of
Littelmann's theorem that the root operators preserve the Lakshmibai–Seshadri paths of shape `λ`;
the other half concerns the Bruhat order and the `a`-chains between consecutive directions.

The proof lowers time–weight graphs. A timed presentation `p` also presents a path in `𝕜 × V`,
its graph, whose first coordinate is time; forgetting time gives the path presented by `p`.
Lowering commutes with forgetting time, for the lifted root `(0, x)` and coroot form `f ∘ snd`
(`TauCeti.PLPath.lower_ofSegments_map_snd`, the case `χ = 0` of
`TauCeti.PLPath.lower_ofSegments_shiftTimed`). The reflection along `(0, x)` and `f ∘ snd` keeps
the time coordinate, so capped reflection of the graph cuts each segment and its duration at the
same fraction, and reflects the velocity of the initial piece by `s_α`. The segments of the
lowered graph thus have positive durations and velocities in `S`, and normalization has merged
the adjacent ones of equal velocity: they form a distinguished presentation of `f_α π`
(`TauCeti.PLPath.isDistinguished_normalize`). When no two distinct points of `S` lie in the same
ray, this is the distinguished presentation of `f_α π`.

## Main results

* `TauCeti.PLPath.isDistinguished_segments_of_lower_eq_some`: if `S` is stable under
  `s = preReflection x f`, the segments of the lowered graph of a duration-one timed presentation
  with velocities in `S` form a distinguished presentation for `S`.
* `TauCeti.PLPath.hasDistinguished_of_lower_eq_some`,
  `TauCeti.PLPath.hasDistinguished_of_raise_eq_some`: **the root operators preserve paths with
  a distinguished presentation for a reflection-stable set `S`**.
* `TauCeti.PLPath.distinguished_of_lower_eq_some`: the distinguished presentation of `f_α π` is
  the segment list of the lowered graph of the distinguished presentation of `π`.
* `TauCeti.LSPath.hasDistinguished_of_lower_eq_some`,
  `TauCeti.LSPath.hasDistinguished_of_raise_eq_some`: lowering or raising an LS path of shape `λ`
  along any root gives a path with velocities in the Weyl orbit `W λ`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 4.
-/

public section

namespace TauCeti.PLPath

open Module Set
open scoped Pointwise

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {S : Set V} {p : List (𝕜 × V)} {π π' : PLPath 𝕜 V} {f : Dual 𝕜 V} {x : V}

/-! ### Lowering time–weight graphs -/

/-- **Lowered time–weight graphs are distinguished.** If `S` is stable under
`s = preReflection x f` and `p` is a duration-one timed presentation with velocities in `S`, the
segments of the lowered time–weight graph of `p` form a distinguished presentation for `S`. -/
theorem isDistinguished_segments_of_lower_eq_some (hS : MapsTo (preReflection x f) S S)
    (hp : IsTimed p) (hd : duration p = 1) (hpS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S)
    {Γ : PLPath 𝕜 (𝕜 × V)}
    (h : lower (f.comp (LinearMap.snd 𝕜 𝕜 V)) (0, x) (ofSegments 𝕜 p) = some Γ) :
    IsDistinguished S Γ.segments := by
  rw [lower_ofSegments, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [listLower_def] at hq
  split_ifs at hq
  cases hq
  rw [segments_ofSegments]
  refine isDistinguished_normalize (fun z hz hz0 ↦ ?_) ?_
  -- Capped reflection of the graph cuts segments at fractions in `[0, 1]` and reflects some
  -- pieces along `(0, x)` and `f ∘ snd`, which keeps durations and reflects velocities by `s`.
  -- The segments of positive duration and velocity in `S` are stable under positive rescaling
  -- and under the reflection of the graph.
  · refine mem_of_mem_reflectRecords (T := {z | 0 < z.1 ∧ z.1⁻¹ • z.2 ∈ S}) ?_ ?_
      (fun z hz ↦ ⟨isTimed_iff.1 hp z hz, hpS z hz⟩) hz hz0
    · rintro a ha z ⟨hz, hzS⟩
      exact ⟨by simpa using mul_pos ha hz, by rwa [Prod.inv_fst_smul_snd_smul ha.ne']⟩
    · rintro z ⟨hz, hzS⟩
      have hz' : preReflection (0, x) (f.comp (LinearMap.snd 𝕜 𝕜 V)) z =
          (z.1, preReflection x f z.2) := by
        ext <;> simp [preReflection_apply]
      rw [Set.mem_ofPred_eq, hz', ← map_smul]
      exact ⟨hz, hS hzS⟩
  · simpa [duration_eq_fst_sum, sum_reflectRecords] using hd

/-- **Lowering preserves distinguished presentations.** If `S` is stable under the reflection
`s = preReflection x f` and `π` has a distinguished presentation for `S`, so does `f_α π`. For a
Lakshmibai–Seshadri path, `S` is the Weyl orbit `W λ`. -/
theorem hasDistinguished_of_lower_eq_some (h : HasDistinguished S π)
    (hS : MapsTo (preReflection x f) S S) (hπ : lower f x π = some π') :
    HasDistinguished S π' := by
  obtain ⟨p, hp, rfl⟩ := hasDistinguished_iff.1 h
  rw [lower_ofSegments_map_snd, Option.map_eq_some_iff] at hπ
  obtain ⟨Γ, hΓ, rfl⟩ := hπ
  have hΓd := isDistinguished_segments_of_lower_eq_some hS hp.isTimed hp.duration_eq_one
    hp.slope_mem hΓ
  simpa [map_def] using hΓd.hasDistinguished

/-- **The distinguished presentation of a lowered path.** If no two distinct points of `S` lie in
the same ray, `S` is stable under `s = preReflection x f`, and `p` is a distinguished presentation
of `π` for `S`, then the distinguished presentation of `f_α π` is the segment list of the lowered
time–weight graph of `p`. -/
theorem distinguished_of_lower_eq_some (hp : IsDistinguished S p)
    (hS : MapsTo (preReflection x f) S S) (hS' : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (h : lower f x (ofSegments 𝕜 (p.map Prod.snd)) = some π') :
    ∃ Γ, lower (f.comp (LinearMap.snd 𝕜 𝕜 V)) (0, x) (ofSegments 𝕜 p) = some Γ ∧
      distinguished S π' = Γ.segments := by
  rw [lower_ofSegments_map_snd, Option.map_eq_some_iff] at h
  obtain ⟨Γ, hΓ, rfl⟩ := h
  refine ⟨Γ, hΓ, ?_⟩
  have hΓd := isDistinguished_segments_of_lower_eq_some hS hp.isTimed hp.duration_eq_one
    hp.slope_mem hΓ
  simpa [map_def] using distinguished_ofSegments hΓd hS'

/-! ### The raising operator -/

/-- **Raising preserves distinguished presentations.** If `S` is stable under the reflection
`s = preReflection x f` and `π` has a distinguished presentation for `S`, so does `e_α π`. -/
theorem hasDistinguished_of_raise_eq_some (h : HasDistinguished S π)
    (hS : MapsTo (preReflection x f) S S) (hπ : raise f x π = some π') :
    HasDistinguished S π' := by
  rw [raise_def, Option.map_eq_some_iff] at hπ
  obtain ⟨ρ, hρ, rfl⟩ := hπ
  -- The set `-S` is stable under the linear reflection `s` too.
  have hS' : MapsTo (preReflection x f) (-S) (-S) := fun u hu ↦ by
    simpa [Set.mem_neg, map_neg] using hS (Set.mem_neg.1 hu)
  simpa using (hasDistinguished_of_lower_eq_some h.reverse hS' hρ).reverse

end TauCeti.PLPath

namespace TauCeti.LSPath

open Module RootPairing Set

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}
  {b : P.Base} [Finite ι] [P.IsReduced] {lam : M} (π : LSPath P b lam)
  {𝕜 : Type*} {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {f : M →+ V}

/-- **Lowering an LS path stays in the Weyl orbit.** For a height form `F` agreeing with the
coroot `αᵢ^∨` on the weight lattice, lowering the realized LS path along the realized root `f αᵢ`
gives a path with a distinguished presentation for the realized orbit `f (W λ)`. -/
theorem hasDistinguished_of_lower_eq_some (i : ι) {F : Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {π' : PLPath 𝕜 V}
    (h : PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some π') :
    PLPath.HasDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) π' := by
  have hS := P.mapsTo_preReflection_image_orbit_weylGroup i hF lam
  rw [MulAction.orbit, ← range_comp] at hS
  exact PLPath.hasDistinguished_of_lower_eq_some (π.hasDistinguished_toPLPath 𝕜 f) hS h

/-- **Raising an LS path stays in the Weyl orbit.** For a height form `F` agreeing with the
coroot `αᵢ^∨` on the weight lattice, raising the realized LS path along the realized root `f αᵢ`
gives a path with a distinguished presentation for the realized orbit `f (W λ)`. -/
theorem hasDistinguished_of_raise_eq_some (i : ι) {F : Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {π' : PLPath 𝕜 V}
    (h : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some π') :
    PLPath.HasDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) π' := by
  have hS := P.mapsTo_preReflection_image_orbit_weylGroup i hF lam
  rw [MulAction.orbit, ← range_comp] at hS
  exact PLPath.hasDistinguished_of_raise_eq_some (π.hasDistinguished_toPLPath 𝕜 f) hS h

end TauCeti.LSPath
