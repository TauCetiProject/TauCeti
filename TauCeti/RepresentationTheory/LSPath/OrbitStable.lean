/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

The proof runs the lowering operator on timed presentations. Capped reflection
`TauCeti.PLPath.reflectRecords` cuts a segment `v` at a fraction `r / f v` and reflects the initial
piece; `TauCeti.PLPath.reflectRecordsTimed` cuts the duration `d` of `v` at the same fraction, so
the reflected piece has velocity `s_α (d⁻¹ • v)` and the kept piece velocity `d⁻¹ • v`. The kept
piece is omitted when it is empty. Merging adjacent segments of equal velocity
(`TauCeti.PLPath.mergeSlopes`) then turns any duration-one timed presentation with velocities in
`S` into a distinguished one. When no two distinct points of `S` lie in the same ray, this gives
the distinguished presentation of `f_α π` explicitly from that of `π`.

## Main definitions

* `TauCeti.PLPath.mergeSlopes`: merge adjacent segments of a timed presentation that have the
  same velocity.
* `TauCeti.PLPath.reflectRecordsTimed`: capped reflection on timed presentations.
* `TauCeti.PLPath.listLowerTimed`: the lowering operator on timed presentations.
* `TauCeti.PLPath.reverseTimed`: the reversal of a timed presentation.

## Main results

* `TauCeti.PLPath.hasDistinguished_ofSegments`: a duration-one timed presentation with velocities
  in `S` presents a path with a distinguished presentation for `S`.
* `TauCeti.PLPath.lower_ofSegments_map_snd`: the lowering operator may be computed on any timed
  presentation, by `TauCeti.PLPath.listLowerTimed`.
* `TauCeti.PLPath.hasDistinguished_of_lower_eq_some`,
  `TauCeti.PLPath.hasDistinguished_of_raise_eq_some`: **the root operators preserve paths with
  a distinguished presentation for a reflection-stable set `S`**.
* `TauCeti.PLPath.distinguished_of_lower_eq_some`: the distinguished presentation of `f_α π`,
  computed from that of `π`.
* `TauCeti.LSPath.hasDistinguished_of_lower_eq_some`,
  `TauCeti.LSPath.hasDistinguished_of_raise_eq_some`: lowering or raising an LS path of dominant
  shape `λ` along any root gives a path with velocities in the Weyl orbit `W λ`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 4.
-/

public section

namespace TauCeti.PLPath

open Module Set
open scoped Pointwise

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {S : Set V} {p q : List (𝕜 × V)} {π π' : PLPath 𝕜 V}

/-! ### Merging adjacent segments of equal velocity -/

open scoped Classical in
/-- Prepend a timed segment `y` to a timed presentation, merging it with the first segment when
both have the same velocity. -/
noncomputable def consMergeSlope (y : 𝕜 × V) : List (𝕜 × V) → List (𝕜 × V)
  | [] => [y]
  | z :: q => if y.1⁻¹ • y.2 = z.1⁻¹ • z.2 then (y.1 + z.1, y.2 + z.2) :: q else y :: z :: q

/-- Merge the adjacent segments of a timed presentation that have the same velocity. On a timed
presentation this does not change the presented path, the total duration or the set of
velocities, and afterwards adjacent segments have different velocities. -/
noncomputable def mergeSlopes (p : List (𝕜 × V)) : List (𝕜 × V) :=
  p.foldr consMergeSlope []

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem consMergeSlope_nil (y : 𝕜 × V) : consMergeSlope y [] = [y] :=
  (rfl)

open scoped Classical in
omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem consMergeSlope_cons (y z : 𝕜 × V) (q : List (𝕜 × V)) :
    consMergeSlope y (z :: q) =
      if y.1⁻¹ • y.2 = z.1⁻¹ • z.2 then (y.1 + z.1, y.2 + z.2) :: q else y :: z :: q :=
  (rfl)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem mergeSlopes_nil : mergeSlopes ([] : List (𝕜 × V)) = [] :=
  (rfl)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem mergeSlopes_cons (y : 𝕜 × V) (p : List (𝕜 × V)) :
    mergeSlopes (y :: p) = consMergeSlope y (mergeSlopes p) :=
  (rfl)

/-- Merging two segments `(d, v)` and `(e, w)` of the same velocity gives a segment of that
velocity. -/
private theorem inv_smul_add_of_inv_smul_eq {y z : 𝕜 × V} (hy : 0 < y.1) (hz : 0 < z.1)
    (h : y.1⁻¹ • y.2 = z.1⁻¹ • z.2) : (y.1 + z.1)⁻¹ • (y.2 + z.2) = z.1⁻¹ • z.2 := by
  obtain ⟨u, hu⟩ : ∃ u, z.1⁻¹ • z.2 = u := ⟨_, rfl⟩
  have hy' : y.2 = y.1 • u := by rw [← hu, ← h, smul_inv_smul₀ hy.ne']
  have hz' : z.2 = z.1 • u := by rw [← hu, smul_inv_smul₀ hz.ne']
  rw [hu, hy', hz', ← add_smul, inv_smul_smul₀ (add_pos hy hz).ne']

theorem isTimed_consMergeSlope {y : 𝕜 × V} (hy : 0 < y.1) (hq : IsTimed q) :
    IsTimed (consMergeSlope y q) := by
  rcases q with _ | ⟨z, q⟩
  · simpa [isTimed_cons] using hy
  obtain ⟨hz, hq⟩ := isTimed_cons.1 hq
  rw [consMergeSlope_cons]
  split_ifs
  · exact isTimed_cons.2 ⟨add_pos hy hz, hq⟩
  · exact isTimed_cons.2 ⟨hy, isTimed_cons.2 ⟨hz, hq⟩⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem duration_consMergeSlope (y : 𝕜 × V) (q : List (𝕜 × V)) :
    duration (consMergeSlope y q) = y.1 + duration q := by
  rcases q with _ | ⟨z, q⟩
  · simp
  rw [consMergeSlope_cons]
  split_ifs <;> simp [add_assoc]

theorem slope_mem_of_mem_consMergeSlope {y : 𝕜 × V} (hy : 0 < y.1) (hq : IsTimed q)
    (hyS : y.1⁻¹ • y.2 ∈ S) (hqS : ∀ z ∈ q, z.1⁻¹ • z.2 ∈ S) :
    ∀ z ∈ consMergeSlope y q, z.1⁻¹ • z.2 ∈ S := by
  rcases q with _ | ⟨z, q⟩
  · simpa using hyS
  have hz := (isTimed_cons.1 hq).1
  rw [consMergeSlope_cons]
  split_ifs with h
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨inv_smul_add_of_inv_smul_eq hy hz h ▸ hqS z (by simp),
      fun w hw ↦ hqS w (List.mem_cons_of_mem _ hw)⟩
  · simp only [List.mem_cons, forall_eq_or_imp] at hqS ⊢
    exact ⟨hyS, hqS⟩

theorem isChain_slope_consMergeSlope {y : 𝕜 × V} (hy : 0 < y.1) (hq : IsTimed q)
    (hchain : (q.map fun z ↦ z.1⁻¹ • z.2).IsChain (· ≠ ·)) :
    ((consMergeSlope y q).map fun z ↦ z.1⁻¹ • z.2).IsChain (· ≠ ·) := by
  rcases q with _ | ⟨z, q⟩
  · simp
  have hz := (isTimed_cons.1 hq).1
  rw [consMergeSlope_cons]
  split_ifs with h
  · simpa only [List.map_cons, inv_smul_add_of_inv_smul_eq hy hz h] using hchain
  · simpa only [List.map_cons, List.isChain_cons_cons] using ⟨h, hchain⟩

theorem ofSegments_map_snd_consMergeSlope {y : 𝕜 × V} (hy : 0 < y.1) (hq : IsTimed q) :
    ofSegments 𝕜 ((consMergeSlope y q).map Prod.snd) = ofSegments 𝕜 (y.2 :: q.map Prod.snd) := by
  rcases q with _ | ⟨z, q⟩
  · simp
  have hz := (isTimed_cons.1 hq).1
  rw [consMergeSlope_cons]
  split_ifs with h
  · -- Both segments are nonnegative multiples of their common velocity.
    obtain ⟨u, hu⟩ : ∃ u, z.1⁻¹ • z.2 = u := ⟨_, rfl⟩
    have hy' : y.2 = y.1 • u := by rw [← hu, ← h, smul_inv_smul₀ hy.ne']
    have hz' : z.2 = z.1 • u := by rw [← hu, smul_inv_smul₀ hz.ne']
    simp only [List.map_cons]
    rw [hy', hz', ofSegments_smul_cons_smul_cons hy.le hz.le, add_smul]
  · rfl

theorem isTimed_mergeSlopes (hp : IsTimed p) : IsTimed (mergeSlopes p) := by
  induction p with
  | nil => exact isTimed_nil
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    exact isTimed_consMergeSlope hy (ih hp)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem duration_mergeSlopes (p : List (𝕜 × V)) : duration (mergeSlopes p) = duration p := by
  induction p with
  | nil => rfl
  | cons y p ih => simp [ih]

theorem slope_mem_of_mem_mergeSlopes (hp : IsTimed p) (hS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S) :
    ∀ z ∈ mergeSlopes p, z.1⁻¹ • z.2 ∈ S := by
  induction p with
  | nil => simp
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    simp only [List.mem_cons, forall_eq_or_imp] at hS
    exact slope_mem_of_mem_consMergeSlope hy (isTimed_mergeSlopes hp) hS.1 (ih hp hS.2)

theorem isChain_slope_mergeSlopes (hp : IsTimed p) :
    ((mergeSlopes p).map fun z ↦ z.1⁻¹ • z.2).IsChain (· ≠ ·) := by
  induction p with
  | nil => simp
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    exact isChain_slope_consMergeSlope hy (isTimed_mergeSlopes hp) (ih hp)

/-- Merging adjacent segments of equal velocity does not change the presented path. -/
@[simp]
theorem ofSegments_map_snd_mergeSlopes (hp : IsTimed p) :
    ofSegments 𝕜 ((mergeSlopes p).map Prod.snd) = ofSegments 𝕜 (p.map Prod.snd) := by
  induction p with
  | nil => rfl
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    rw [mergeSlopes_cons, ofSegments_map_snd_consMergeSlope hy (isTimed_mergeSlopes hp),
      ofSegments_cons, ih hp, List.map_cons, ofSegments_cons]

/-- Merging adjacent segments of equal velocity turns a duration-one timed presentation with
velocities in `S` into a distinguished presentation for `S`. -/
theorem isDistinguished_mergeSlopes (hp : IsTimed p) (hd : duration p = 1)
    (hS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S) : IsDistinguished S (mergeSlopes p) :=
  ⟨isTimed_mergeSlopes hp, by rw [duration_mergeSlopes, hd], slope_mem_of_mem_mergeSlopes hp hS,
    isChain_slope_mergeSlopes hp⟩

/-- A path with a timed presentation of duration `1` and velocities in `S` has a distinguished
presentation for `S`. -/
theorem hasDistinguished_ofSegments (hp : IsTimed p) (hd : duration p = 1)
    (hS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S) : HasDistinguished S (ofSegments 𝕜 (p.map Prod.snd)) :=
  ofSegments_map_snd_mergeSlopes hp ▸ (isDistinguished_mergeSlopes hp hd hS).hasDistinguished

/-! ### The lowering operator on timed presentations -/

section Lower

variable (f : Dual 𝕜 V) (x : V)

/-- Capped reflection `TauCeti.PLPath.reflectRecords` on timed presentations. When the segment
`v` of duration `d` is cut at the fraction `r / f v`, so is its duration: the reflected initial
piece `s ((r / f v) • v)` gets duration `d * (r / f v)`, and the kept piece `(1 - r / f v) • v`
duration `d * (1 - r / f v)`. The kept piece is omitted when it is empty, that is when
`r = f v`. -/
def reflectRecordsTimed (c : 𝕜) : List (𝕜 × V) → List (𝕜 × V)
  | [] => []
  | y :: p =>
    if 0 < min (f y.2 + listMinHeight f (p.map Prod.snd)) c then
      if min (f y.2 + listMinHeight f (p.map Prod.snd)) c < f y.2 then
        (y.1 * (min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2),
            preReflection x f ((min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2) • y.2)) ::
          (y.1 * (1 - min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2),
            (1 - min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2) • y.2) ::
          reflectRecordsTimed (c - f y.2) p
      else (y.1, preReflection x f y.2) :: reflectRecordsTimed (c - f y.2) p
    else y :: reflectRecordsTimed (c - f y.2) p

/-- Littelmann's lowering operator on timed presentations, computed by
`TauCeti.PLPath.reflectRecordsTimed` exactly as `TauCeti.PLPath.listLower` is computed by
`TauCeti.PLPath.reflectRecords`. -/
def listLowerTimed (p : List (𝕜 × V)) : Option (List (𝕜 × V)) :=
  if 1 ≤ f (p.map Prod.snd).sum - listMinHeight f (p.map Prod.snd) then
    some (reflectRecordsTimed f x (listMinHeight f (p.map Prod.snd) + 1) p)
  else none

variable {f x} {c : 𝕜}

/-- The cut fraction of a segment whose initial piece is reflected lies in `(0, 1]`. -/
private theorem cut_pos_and_le {v : V} {l : List V}
    (h : 0 < min (f v + listMinHeight f l) c) :
    0 < f v ∧ 0 < min (f v + listMinHeight f l) c / f v ∧
      min (f v + listMinHeight f l) c / f v ≤ 1 := by
  have hle : min (f v + listMinHeight f l) c ≤ f v :=
    (min_le_left _ _).trans (by linarith [listMinHeight_nonpos (f := f) l])
  have hfv : 0 < f v := h.trans_le hle
  exact ⟨hfv, div_pos h hfv, (div_le_one hfv).2 hle⟩

/-- Timed capped reflection presents the same path as capped reflection of the segments. -/
theorem ofSegments_map_snd_reflectRecordsTimed (c : 𝕜) (p : List (𝕜 × V)) :
    ofSegments 𝕜 ((reflectRecordsTimed f x c p).map Prod.snd) =
      ofSegments 𝕜 (reflectRecords f x c (p.map Prod.snd)) := by
  induction p generalizing c with
  | nil => simp [reflectRecordsTimed]
  | cons y p ih =>
    rw [List.map_cons]
    unfold reflectRecordsTimed
    split_ifs with h₁ h₂
    · simp only [List.map_cons, reflectRecords_cons_of_pos h₁, ofSegments_cons, ih]
    · -- The kept piece `(1 - 1) • v` of `reflectRecords` is stationary.
      have hr : min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2 = 1 :=
        le_antisymm (cut_pos_and_le h₁).2.2 ((le_div_iff₀ (cut_pos_and_le h₁).1).2
          (by simpa using not_lt.1 h₂))
      simp only [List.map_cons, reflectRecords_cons_of_pos h₁, hr, one_smul, sub_self,
        zero_smul, ofSegments_cons, straight_zero, one_mul, ih]
    · simp only [List.map_cons, reflectRecords_cons_of_nonpos (not_lt.1 h₁), ofSegments_cons, ih]

theorem isTimed_reflectRecordsTimed (c : 𝕜) (hp : IsTimed p) :
    IsTimed (reflectRecordsTimed f x c p) := by
  induction p generalizing c with
  | nil => exact isTimed_nil
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    unfold reflectRecordsTimed
    split_ifs with h₁ h₂
    · obtain ⟨hfv, hr, -⟩ := cut_pos_and_le h₁
      refine isTimed_cons.2 ⟨mul_pos hy hr, isTimed_cons.2 ⟨mul_pos hy ?_, ih _ hp⟩⟩
      rw [sub_pos, div_lt_one hfv]
      exact h₂
    · exact isTimed_cons.2 ⟨hy, ih _ hp⟩
    · exact isTimed_cons.2 ⟨hy, ih _ hp⟩

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem duration_reflectRecordsTimed (c : 𝕜) (p : List (𝕜 × V)) :
    duration (reflectRecordsTimed f x c p) = duration p := by
  induction p generalizing c with
  | nil => rfl
  | cons y p ih =>
    unfold reflectRecordsTimed
    split_ifs
    · simp only [duration_cons, ih]
      ring
    · simp [ih]
    · simp [ih]

/-- Timed capped reflection changes velocities only by the reflection `s = preReflection x f`: if
`S` is stable under `s` and contains the velocities of `p`, it contains the velocities of the
timed capped reflection of `p`. -/
theorem slope_mem_of_mem_reflectRecordsTimed (hS : MapsTo (preReflection x f) S S) (c : 𝕜)
    (hp : IsTimed p) (hpS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S) :
    ∀ z ∈ reflectRecordsTimed f x c p, z.1⁻¹ • z.2 ∈ S := by
  induction p generalizing c with
  | nil => simp [reflectRecordsTimed]
  | cons y p ih =>
    obtain ⟨hy, hp⟩ := isTimed_cons.1 hp
    simp only [List.mem_cons, forall_eq_or_imp] at hpS
    obtain ⟨hyS, hpS⟩ := hpS
    -- A reflected piece of `y`, of any positive fraction `a`, runs at velocity `s (y.1⁻¹ • y.2)`.
    have hrefl {a : 𝕜} (ha : 0 < a) :
        (y.1 * a)⁻¹ • preReflection x f (a • y.2) = preReflection x f (y.1⁻¹ • y.2) := by
      rw [map_smul, map_smul, smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
    unfold reflectRecordsTimed
    split_ifs with h₁ h₂
    · obtain ⟨hfv, hr, -⟩ := cut_pos_and_le h₁
      have hkeep : (0 : 𝕜) < 1 - min (f y.2 + listMinHeight f (p.map Prod.snd)) c / f y.2 := by
        rw [sub_pos, div_lt_one hfv]
        exact h₂
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨by simpa only [hrefl hr] using hS hyS, ?_, ih _ hp hpS⟩
      rw [smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hkeep.ne', mul_one]
      exact hyS
    · simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨?_, ih _ hp hpS⟩
      rw [← map_smul]
      exact hS hyS
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hyS, ih _ hp hpS⟩

omit [IsStrictOrderedRing 𝕜] in
theorem listLowerTimed_def (p : List (𝕜 × V)) :
    listLowerTimed f x p = if 1 ≤ f (p.map Prod.snd).sum - listMinHeight f (p.map Prod.snd) then
      some (reflectRecordsTimed f x (listMinHeight f (p.map Prod.snd) + 1) p) else none :=
  (rfl)

/-- **The lowering operator may be computed on any timed presentation.** -/
theorem lower_ofSegments_map_snd (p : List (𝕜 × V)) :
    lower f x (ofSegments 𝕜 (p.map Prod.snd)) =
      (listLowerTimed f x p).map fun q ↦ ofSegments 𝕜 (q.map Prod.snd) := by
  rw [lower_ofSegments, listLower_def, listLowerTimed_def]
  split_ifs
  · simp [ofSegments_map_snd_reflectRecordsTimed]
  · rfl

/-- If `S` is stable under `s = preReflection x f`, lowering a path presented by a timed
presentation of duration `1` with velocities in `S` gives a path presented by such a timed
presentation, namely the timed lowering. -/
theorem exists_listLowerTimed_eq_some (hS : MapsTo (preReflection x f) S S) (hp : IsTimed p)
    (hpS : ∀ z ∈ p, z.1⁻¹ • z.2 ∈ S) (h : lower f x (ofSegments 𝕜 (p.map Prod.snd)) = some π') :
    ∃ q, listLowerTimed f x p = some q ∧ IsTimed q ∧ duration q = duration p ∧
      (∀ z ∈ q, z.1⁻¹ • z.2 ∈ S) ∧ ofSegments 𝕜 (q.map Prod.snd) = π' := by
  rw [lower_ofSegments_map_snd, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q, hq, ?_⟩
  rw [listLowerTimed_def] at hq
  split_ifs at hq
  cases hq
  exact ⟨isTimed_reflectRecordsTimed _ hp, duration_reflectRecordsTimed _ _,
    slope_mem_of_mem_reflectRecordsTimed hS _ hp hpS, rfl⟩

/-- **Lowering preserves distinguished presentations.** If `S` is stable under the reflection
`s = preReflection x f` and `π` has a distinguished presentation for `S`, so does `f_α π`. For a
Lakshmibai–Seshadri path, `S` is the Weyl orbit `W λ`. -/
theorem hasDistinguished_of_lower_eq_some (h : HasDistinguished S π)
    (hS : MapsTo (preReflection x f) S S) (hπ : lower f x π = some π') :
    HasDistinguished S π' := by
  obtain ⟨p, hp, rfl⟩ := hasDistinguished_iff.1 h
  obtain ⟨q, -, hq, hqd, hqS, rfl⟩ := exists_listLowerTimed_eq_some hS hp.isTimed hp.slope_mem hπ
  exact hasDistinguished_ofSegments hq (hqd.trans hp.duration_eq_one) hqS

/-- **The distinguished presentation of a lowered path.** If no two distinct points of `S` lie in
the same ray, `S` is stable under `s = preReflection x f`, and `p` is a distinguished presentation
of `π` for `S`, then the distinguished presentation of `f_α π` is obtained from the timed lowering
of `p` by merging adjacent segments of equal velocity. -/
theorem distinguished_of_lower_eq_some (hp : IsDistinguished S p)
    (hS : MapsTo (preReflection x f) S S) (hS' : S.Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (h : lower f x (ofSegments 𝕜 (p.map Prod.snd)) = some π') :
    ∃ q, listLowerTimed f x p = some q ∧ distinguished S π' = mergeSlopes q := by
  obtain ⟨q, hq, hqt, hqd, hqS, rfl⟩ := exists_listLowerTimed_eq_some hS hp.isTimed hp.slope_mem h
  refine ⟨q, hq, ?_⟩
  rw [← ofSegments_map_snd_mergeSlopes hqt,
    distinguished_ofSegments (isDistinguished_mergeSlopes hqt (hqd.trans hp.duration_eq_one) hqS)
      hS']

end Lower

/-! ### Reversal and the raising operator -/

/-- The reversal of a timed presentation: the segments are negated and traversed in the opposite
order, each in its own time. It presents the reversed path. -/
def reverseTimed (p : List (𝕜 × V)) : List (𝕜 × V) :=
  (p.map fun z ↦ (z.1, -z.2)).reverse

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Module 𝕜 V] in
theorem reverseTimed_def (p : List (𝕜 × V)) :
    reverseTimed p = (p.map fun z ↦ (z.1, -z.2)).reverse :=
  (rfl)

@[simp]
theorem ofSegments_map_snd_reverseTimed (p : List (𝕜 × V)) :
    ofSegments 𝕜 ((reverseTimed p).map Prod.snd) = (ofSegments 𝕜 (p.map Prod.snd)).reverse := by
  simp [reverseTimed_def, List.map_reverse, Function.comp_def]

omit [IsStrictOrderedRing 𝕜] in
/-- Reversing a distinguished presentation for `S` gives a distinguished presentation for `-S`
of the reversed path. -/
theorem IsDistinguished.reverseTimed (hp : IsDistinguished S p) :
    IsDistinguished (-S) (reverseTimed p) := by
  have hslope (z : 𝕜 × V) : (fun y : 𝕜 × V ↦ y.1⁻¹ • y.2) (z.1, -z.2) = -(z.1⁻¹ • z.2) :=
    smul_neg _ _
  refine ⟨isTimed_iff.2 fun z hz ↦ ?_, ?_, fun z hz ↦ ?_, ?_⟩
  · simp only [reverseTimed_def, List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact isTimed_iff.1 hp.isTimed y hy
  · simpa [reverseTimed_def, duration_def, List.map_reverse, Function.comp_def] using
      hp.duration_eq_one
  · simp only [reverseTimed_def, List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [Set.mem_neg, smul_neg, neg_neg]
    exact hp.slope_mem y hy
  · rw [reverseTimed_def, List.map_reverse, List.map_map, List.isChain_reverse]
    have := hp.isChain_slope
    rw [List.isChain_map] at this ⊢
    exact this.imp fun y z hyz ↦ by simpa [Function.comp_def, hslope] using hyz.symm

/-- A path with a distinguished presentation for `S` has reverse with a distinguished
presentation for `-S`. -/
theorem HasDistinguished.reverse (h : HasDistinguished S π) : HasDistinguished (-S) π.reverse := by
  obtain ⟨p, hp, rfl⟩ := hasDistinguished_iff.1 h
  exact hasDistinguished_iff.2 ⟨_, hp.reverseTimed, ofSegments_map_snd_reverseTimed p⟩

/-- **Raising preserves distinguished presentations.** If `S` is stable under the reflection
`s = preReflection x f` and `π` has a distinguished presentation for `S`, so does `e_α π`. -/
theorem hasDistinguished_of_raise_eq_some {f : Dual 𝕜 V} {x : V} (h : HasDistinguished S π)
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
  {b : P.Base} [Finite ι] [P.IsReduced] [P.flip.IsReduced] {lam : M} (π : LSPath P b lam)
  {𝕜 : Type*} {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {f : M →+ V}

omit [Finite ι] [P.IsReduced] [P.flip.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The realized Weyl orbit `f (W λ)` is stable under the reflection in a realized root `f αᵢ`
along a height form agreeing with the coroot `αᵢ^∨` on the weight lattice. -/
theorem mapsTo_preReflection_range_weylGroup (i : ι) {F : Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    MapsTo (preReflection (f (P.root i)) F) (range fun w : P.weylGroup ↦ f (w • lam))
      (range fun w : P.weylGroup ↦ f (w • lam)) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨weylGroup.ofIdx P i * w, ?_⟩
  dsimp only
  rw [mul_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul, P.reflection_apply, map_sub,
    map_zsmul, preReflection_apply, hF, Int.cast_smul_eq_zsmul]

/-- **Lowering an LS path stays in the Weyl orbit.** For dominant `λ`, a realization `f`
injective on `W λ`, and a height form `F` agreeing with the coroot `αᵢ^∨` on the weight lattice,
lowering the realized LS path along the realized root `f αᵢ` gives a path with a distinguished
presentation for the realized orbit `f (W λ)`. -/
theorem hasDistinguished_of_lower_eq_some (hlam : lam ∈ dominantChamber P b)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam)) (i : ι) {F : Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {π' : PLPath 𝕜 V}
    (h : PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some π') :
    PLPath.HasDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) π' := by
  rw [toPLPath_def] at h
  exact PLPath.hasDistinguished_of_lower_eq_some
    (π.isDistinguished_timed 𝕜 f hlam hf).hasDistinguished
    (mapsTo_preReflection_range_weylGroup i hF) h

/-- **Raising an LS path stays in the Weyl orbit.** For dominant `λ`, a realization `f`
injective on `W λ`, and a height form `F` agreeing with the coroot `αᵢ^∨` on the weight lattice,
raising the realized LS path along the realized root `f αᵢ` gives a path with a distinguished
presentation for the realized orbit `f (W λ)`. -/
theorem hasDistinguished_of_raise_eq_some (hlam : lam ∈ dominantChamber P b)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam)) (i : ι) {F : Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {π' : PLPath 𝕜 V}
    (h : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some π') :
    PLPath.HasDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) π' := by
  rw [toPLPath_def] at h
  exact PLPath.hasDistinguished_of_raise_eq_some
    (π.isDistinguished_timed 𝕜 f hlam hf).hasDistinguished
    (mapsTo_preReflection_range_weylGroup i hF) h

end TauCeti.LSPath
