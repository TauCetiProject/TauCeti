/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Lakshmibai–Seshadri paths from linked lists of directions

A Lakshmibai–Seshadri path of shape `λ` (`TauCeti.LSPath`) is recorded by strictly decreasing
directions `τ₀ > ⋯ > τ_l` in `W / W_λ` and break times `0 = a₀ < ⋯ < a_{l+1} = 1`, linked at each
internal break `a` by an `a`-chain. Operations on paths, such as Littelmann's root operators,
naturally produce lists of directions with durations in which a direction may repeat, or a segment
may have duration `0`. This file packages such lists.

A list `[(τ₀, d₀), …, (τ_l, d_l)]` of Weyl group elements with durations is *linked*, starting at
time `t` (`TauCeti.LSPath.Linked`), when consecutive directions are joined by an `a`-chain at
each break `a = t + d₀ + ⋯ + d_k`; repeated consecutive directions are joined by the chain of
length `0`. The directions and durations of an LS path form a linked list starting at time `0`
(`TauCeti.LSPath.linked_dirDurations`). Conversely, a linked list of minimal coset
representatives with nonnegative durations adding up to `1` defines an LS path
(`TauCeti.LSPath.ofLinked`): dropping the entries of duration `0` and merging consecutive entries
with the same direction keeps the list linked, since the chains at a dropped entry are
concatenated, and it does not change the piecewise-linear path that the list presents
(`TauCeti.LSPath.toPLPath_ofLinked`).

## Main definitions

* `TauCeti.LSPath.Linked`: the chain condition on a list of directions with durations.
* `TauCeti.LSPath.dirDurations`: the directions of an LS path with the durations of its segments.
* `TauCeti.LSPath.ofLinked`: the LS path presented by a linked list.

## Main results

* `TauCeti.LSPath.linked_iff_getElem`: a list is linked exactly when each of its breaks carries an
  `a`-chain at the total duration before it.
* `TauCeti.LSPath.Linked.split`: subdividing an entry keeps a list linked.
* `TauCeti.LSPath.Linked.exists_sum_take_sub_mul_eq_intCast`: along a linked list, the height at a
  break `a` before the direction `τ` differs from `a ⟨τ λ, -⟩` by an integer.
* `TauCeti.LSPath.linked_dirDurations` and `TauCeti.LSPath.map_snd_timed`: the directions and
  durations of an LS path form a linked list presenting its path.
* `TauCeti.LSPath.toPLPath_ofLinked`: **the LS path of a linked list presents the path of the
  list**.
* `TauCeti.LSPath.dirDurations_ofLinked` and `TauCeti.LSPath.ofLinked_dirDurations`: on lists with
  positive durations and distinct consecutive directions, `TauCeti.LSPath.ofLinked` inverts
  `TauCeti.LSPath.dirDurations`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} {lam : M}

/-! ### Merging repeated directions -/

section Merge

open scoped Classical in
/-- Prepend an entry to a list of directions with durations, dropping it if its duration is `0` and
merging it into the first entry if they have the same direction. -/
private noncomputable def consMergeDir (p : P.weylGroup × ℚ) :
    List (P.weylGroup × ℚ) → List (P.weylGroup × ℚ)
  | [] => if p.2 = 0 then [] else [p]
  | q :: l => if p.2 = 0 then q :: l else if p.1 = q.1 then (p.1, p.2 + q.2) :: l else p :: q :: l

/-- Drop the entries of duration `0` and merge consecutive entries with the same direction. -/
private noncomputable def mergeDirs (l : List (P.weylGroup × ℚ)) : List (P.weylGroup × ℚ) :=
  l.foldr consMergeDir []

private theorem mergeDirs_cons (p : P.weylGroup × ℚ) (l : List (P.weylGroup × ℚ)) :
    mergeDirs (p :: l) = consMergeDir p (mergeDirs l) :=
  List.foldr_cons

private theorem consMergeDir_of_eq_zero {p : P.weylGroup × ℚ} (hp : p.2 = 0)
    (l : List (P.weylGroup × ℚ)) : consMergeDir p l = l := by
  cases l <;> simp [consMergeDir, hp]

private theorem fst_of_mem_head?_consMergeDir {p : P.weylGroup × ℚ} (hp : p.2 ≠ 0)
    {l : List (P.weylGroup × ℚ)} {q : P.weylGroup × ℚ} (hq : q ∈ (consMergeDir p l).head?) :
    q.1 = p.1 := by
  cases l with
  | nil => simp_all [consMergeDir]
  | cons r l =>
    by_cases h : p.1 = r.1 <;> simp_all [consMergeDir, eq_comm]

private theorem mem_consMergeDir {p q : P.weylGroup × ℚ} {l : List (P.weylGroup × ℚ)}
    (hq : q ∈ consMergeDir p l) :
    q ∈ l ∨ q.1 = p.1 ∧ p.2 ≠ 0 ∧ (q.2 = p.2 ∨ ∃ r ∈ l.head?, q.2 = p.2 + r.2) := by
  cases l with
  | nil => by_cases hp : p.2 = 0 <;> simp_all [consMergeDir]
  | cons r l =>
    by_cases hp : p.2 = 0
    · simp_all [consMergeDir]
    · by_cases hpr : p.1 = r.1
      · simp only [consMergeDir, hp, hpr, ↓reduceIte, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Or.inr ⟨by simp [hpr], hp, Or.inr ⟨r, rfl, rfl⟩⟩
        · exact Or.inl (List.mem_cons_of_mem _ hq)
      · simp only [consMergeDir, hp, hpr, ↓reduceIte, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Or.inr ⟨rfl, hp, Or.inl rfl⟩
        · exact Or.inl (List.mem_cons.mpr hq)

private theorem exists_mem_of_mem_mergeDirs {l : List (P.weylGroup × ℚ)} {q : P.weylGroup × ℚ}
    (hq : q ∈ mergeDirs l) : ∃ p ∈ l, p.1 = q.1 := by
  induction l generalizing q with
  | nil => simp [mergeDirs] at hq
  | cons p l ih =>
    rw [mergeDirs_cons] at hq
    rcases mem_consMergeDir hq with hq | ⟨hq, -⟩
    · obtain ⟨p', hp', h⟩ := ih hq
      exact ⟨p', List.mem_cons_of_mem _ hp', h⟩
    · exact ⟨p, List.mem_cons_self, hq.symm⟩

private theorem pos_of_mem_mergeDirs {l : List (P.weylGroup × ℚ)} (hl : ∀ p ∈ l, 0 ≤ p.2)
    {q : P.weylGroup × ℚ} (hq : q ∈ mergeDirs l) : 0 < q.2 := by
  induction l generalizing q with
  | nil => simp [mergeDirs] at hq
  | cons p l ih =>
    rw [mergeDirs_cons] at hq
    have ih' := fun {r} (hr : r ∈ mergeDirs l) ↦ ih (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr)) hr
    have hp0 := hl p List.mem_cons_self
    rcases mem_consMergeDir hq with hq | ⟨-, hp, hq | ⟨r, hr, hq⟩⟩
    · exact ih' hq
    · exact hq ▸ lt_of_le_of_ne hp0 (Ne.symm hp)
    · exact hq ▸ add_pos_of_nonneg_of_pos hp0 (ih' (List.mem_of_mem_head? hr))

private theorem sum_map_snd_mergeDirs (l : List (P.weylGroup × ℚ)) :
    ((mergeDirs l).map Prod.snd).sum = (l.map Prod.snd).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [mergeDirs_cons, List.map_cons, List.sum_cons, ← ih]
    rcases mergeDirs l with _ | ⟨r, l'⟩
    · by_cases hp : p.2 = 0 <;> simp [consMergeDir, hp]
    · by_cases hp : p.2 = 0
      · simp [consMergeDir, hp]
      · by_cases hpr : p.1 = r.1 <;> simp [consMergeDir, hp, hpr, add_assoc]

private theorem isChain_mergeDirs (l : List (P.weylGroup × ℚ)) :
    (mergeDirs l).IsChain fun p q ↦ p.1 ≠ q.1 := by
  induction l with
  | nil => simp [mergeDirs]
  | cons p l ih =>
    rw [mergeDirs_cons]
    rcases hL : mergeDirs l with _ | ⟨r, l'⟩
    · by_cases hp : p.2 = 0 <;> simp [consMergeDir, hp]
    · rw [hL] at ih
      by_cases hp : p.2 = 0
      · simpa [consMergeDir, hp] using ih
      · by_cases hpr : p.1 = r.1
        · simp only [consMergeDir, hp, hpr, ↓reduceIte]
          cases l' with
          | nil => simp
          | cons s l' =>
            rw [List.isChain_cons_cons] at ih ⊢
            exact ih
        · simp only [consMergeDir, hp, hpr, ↓reduceIte]
          exact List.isChain_cons_cons.mpr ⟨hpr, ih⟩

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V]

private theorem ofSegments_map_mergeDirs (f : M →+ V) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) :
    PLPath.ofSegments 𝕜 ((mergeDirs l).map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) =
      PLPath.ofSegments 𝕜 (l.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hpos := fun {q} (hq : q ∈ mergeDirs l) ↦
      pos_of_mem_mergeDirs (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr)) hq
    rw [mergeDirs_cons, List.map_cons, PLPath.ofSegments_cons, ← ih fun r hr ↦
      hl r (List.mem_cons_of_mem _ hr), ← PLPath.ofSegments_cons]
    generalize mergeDirs l = L at hpos ⊢
    by_cases hp : p.2 = 0
    · rw [consMergeDir_of_eq_zero hp, hp, Rat.cast_zero, zero_smul, PLPath.ofSegments_zero_cons]
    rcases L with _ | ⟨r, L⟩
    · simp [consMergeDir, hp]
    · by_cases hpr : p.1 = r.1
      · simp only [consMergeDir, hp, hpr, ↓reduceIte, List.map_cons, Rat.cast_add]
        rw [PLPath.ofSegments_smul_cons_smul_cons (Rat.cast_nonneg.mpr (hl p List.mem_cons_self))
          (Rat.cast_nonneg.mpr (hpos List.mem_cons_self).le)]
      · simp [consMergeDir, hp, hpr]

private theorem mergeDirs_eq_self {l : List (P.weylGroup × ℚ)} (hpos : ∀ p ∈ l, 0 < p.2)
    (hne : l.IsChain fun p q ↦ p.1 ≠ q.1) : mergeDirs l = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [mergeDirs_cons, ih (fun q hq ↦ hpos q (List.mem_cons_of_mem _ hq)) hne.tail]
    have hp : p.2 ≠ 0 := (hpos p List.mem_cons_self).ne'
    cases l with
    | nil => simp [consMergeDir, hp]
    | cons q l => simp [consMergeDir, hp, (List.isChain_cons_cons.mp hne).1]

private theorem length_mergeDirs_pos {l : List (P.weylGroup × ℚ)}
    (hsum : (l.map Prod.snd).sum = 1) : 0 < (mergeDirs l).length :=
  List.length_pos_iff.mpr fun h ↦ by simpa [h] using (sum_map_snd_mergeDirs l).trans hsum

end Merge


variable [Finite ι] [P.IsReduced]

/-! ### Linked lists of directions -/

variable (P b lam) in
/-- A list `[(τ₀, d₀), …, (τ_l, d_l)]` of Weyl group elements with durations is **linked**,
starting at time `t`, when for each break, at time `a = t + d₀ + ⋯ + d_k`, some saturated chain of
`W / W_λ` from `τ_k` down to `τ_{k+1}` is an `a`-chain. Consecutive directions may coincide, joined
by the chain of length `0`. These are the conditions on the directions and breaks of a
Lakshmibai–Seshadri path (`TauCeti.LSPath`), before merging repeated directions. -/
def Linked : ℚ → List (P.weylGroup × ℚ) → Prop
  | _, [] => True
  | _, [_] => True
  | t, p :: q :: l => (∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = p.1 ∧ C.last.1 = q.1 ∧ IsAChain (t + p.2) lam C) ∧ Linked (t + p.2) (q :: l)

@[simp]
theorem linked_nil (t : ℚ) : Linked P b lam t [] :=
  trivial

@[simp]
theorem linked_singleton (t : ℚ) (p : P.weylGroup × ℚ) : Linked P b lam t [p] :=
  trivial

@[simp]
theorem linked_cons_cons {t : ℚ} {p q : P.weylGroup × ℚ} {l : List (P.weylGroup × ℚ)} :
    Linked P b lam t (p :: q :: l) ↔
      (∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
        C.head.1 = p.1 ∧ C.last.1 = q.1 ∧ IsAChain (t + p.2) lam C) ∧
      Linked P b lam (t + p.2) (q :: l) :=
  Iff.rfl

/-- A list `p :: l` is linked when `p` is joined to the first entry of `l` and `l` is linked from
the end of `p`. -/
theorem linked_cons_iff {t : ℚ} {p : P.weylGroup × ℚ} {l : List (P.weylGroup × ℚ)} :
    Linked P b lam t (p :: l) ↔
      (∀ q ∈ l.head?, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
        C.head.1 = p.1 ∧ C.last.1 = q.1 ∧ IsAChain (t + p.2) lam C) ∧
      Linked P b lam (t + p.2) l := by
  cases l <;> simp

/-- A list is linked exactly when each break, at the total duration before it, is joined by an
`a`-chain. -/
theorem linked_iff_getElem {t : ℚ} {l : List (P.weylGroup × ℚ)} :
    Linked P b lam t l ↔ ∀ k (hk : k + 1 < l.length),
      ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
        C.head.1 = l[k].1 ∧ C.last.1 = l[k + 1].1 ∧
          IsAChain (t + ((l.take (k + 1)).map Prod.snd).sum) lam C := by
  induction l generalizing t with
  | nil => simp
  | cons p l ih =>
    rw [linked_cons_iff, ih]
    cases l with
    | nil => simp
    | cons q l =>
      constructor
      · rintro ⟨h₀, h⟩ k hk
        cases k with
        | zero => simpa using h₀ q rfl
        | succ k =>
          obtain ⟨C, h₁, h₂, h₃⟩ := h k (by simpa using hk)
          exact ⟨C, by simpa using h₁, by simpa using h₂, by simpa [add_assoc] using h₃⟩
      · intro h
        refine ⟨fun r hr ↦ ?_, fun k hk ↦ ?_⟩
        · obtain rfl : q = r := by simpa using hr
          simpa using h 0 (by simp)
        · simpa [add_assoc] using h (k + 1) (by simpa using hk)

/-- Splitting an entry `(w, d₁ + d₂)` of a linked list into two consecutive entries `(w, d₁)` and
`(w, d₂)` keeps it linked. -/
theorem Linked.split {t : ℚ} {l₁ l₂ : List (P.weylGroup × ℚ)} {w : P.weylGroup} {d₁ d₂ : ℚ}
    (hw : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w)
    (h : Linked P b lam t (l₁ ++ (w, d₁ + d₂) :: l₂)) :
    Linked P b lam t (l₁ ++ (w, d₁) :: (w, d₂) :: l₂) := by
  induction l₁ generalizing t with
  | nil =>
    refine ⟨⟨RelSeries.singleton _ ⟨w, hw⟩, rfl, rfl, isAChain_singleton _⟩, ?_⟩
    rw [List.nil_append, linked_cons_iff] at h
    rw [linked_cons_iff]
    simpa [add_assoc] using h
  | cons p l₁ ih =>
    rw [List.cons_append, linked_cons_iff] at h ⊢
    refine ⟨?_, ih h.2⟩
    cases l₁ <;> simpa using h.1

/-- **Heights at breaks, up to integers.** Along a linked list starting at time `0`, the height
`∑_{m < j} d_m g(τ_m λ)` at the `j`-th break differs by an integer from `a_j g(τ_j λ)`, where
`a_j = ∑_{m < j} d_m`, for every integral linear form `g`. This is
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain` for the break times of the list. -/
theorem Linked.exists_sum_take_sub_mul_eq_intCast [P.flip.IsReduced]
    (hlam : lam ∈ dominantChamber P b) {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (g : Module.Dual ℤ M) {j : ℕ} (hj : j < l.length) :
    ∃ z : ℤ, ((l.take j).map fun p ↦ p.2 * (g (p.1 • lam) : ℚ)).sum -
      ((l.take j).map Prod.snd).sum * g (l[j].1 • lam) = z := by
  set t : ℕ → ℚ := fun k ↦ ((l.take k).map Prod.snd).sum with ht
  set τ : ℕ → P.weylGroup := fun k ↦ (l.getD k (1, 0)).1 with hτ
  have hτl : ∀ k (hk : k < l.length), τ k = l[k].1 := fun k hk ↦ by
    simp [τ, List.getElem?_eq_getElem hk]
  have ht_succ : ∀ k (hk : k < l.length), t (k + 1) = t k + l[k].2 := fun k hk ↦ by
    simp only [t]
    rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append]
    simp
  -- The height at a break is the sum over the segments before it.
  have hhgt : ∀ k ≤ l.length, ((l.take k).map fun p ↦ p.2 * (g (p.1 • lam) : ℚ)).sum =
      ∑ m ∈ Finset.range k, (t (m + 1) - t m) * g (τ m • lam) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append,
        ih (by omega), Finset.sum_range_succ, ht_succ k (by omega), hτl k (by omega)]
      simp
  obtain ⟨z, hz⟩ := exists_sum_sub_mul_eq_intCast_of_isAChain hlam (s := l.length) (τ := τ)
    (t := t) (by simp [t])
    (fun k hk ↦ by
      obtain ⟨C, h₁, h₂, h₃⟩ := linked_iff_getElem.mp hl k hk
      exact ⟨C, by rw [hτl k (by omega), h₁], by rw [hτl (k + 1) hk, h₂], by simpa [t] using h₃⟩)
    g hj
  rw [Finset.sum_range_succ, ← hhgt j hj.le, hτl j hj, ht_succ j hj] at hz
  exact ⟨z, by linear_combination hz⟩

/-! ### Merging linked lists -/

/-- If `x` is joined to the first entry of a linked list, then also to the first entry after
merging: dropped entries of duration `0` sit at the same break, and their chains are
concatenated. -/
private theorem exists_isAChain_head?_mergeDirs {T : ℚ} {l : List (P.weylGroup × ℚ)}
    (hl : Linked P b lam T l) {x : P.weylGroup}
    (hx : ∀ p ∈ l.head?, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = x ∧ C.last.1 = p.1 ∧ IsAChain T lam C) :
    ∀ q ∈ (mergeDirs l).head?, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = x ∧ C.last.1 = q.1 ∧ IsAChain T lam C := by
  induction l with
  | nil => simp [mergeDirs]
  | cons p l ih =>
    intro q hq
    rw [mergeDirs_cons] at hq
    obtain ⟨C, hCx, hCp, hC⟩ := hx p rfl
    by_cases hp : p.2 = 0
    · rw [consMergeDir_of_eq_zero hp] at hq
      rw [linked_cons_iff, hp, add_zero] at hl
      refine ih hl.2 (fun r hr ↦ ?_) q hq
      obtain ⟨D, hDp, hDr, hD⟩ := hl.1 r hr
      have hjoin : C.last = D.head := Subtype.ext (hCp.trans hDp.symm)
      exact ⟨C.smash D hjoin, by simpa using hCx, by simpa using hDr,
        (isAChain_smash_iff hjoin).mpr ⟨hC, hD⟩⟩
    · exact ⟨C, hCx, by rw [hCp, fst_of_mem_head?_consMergeDir hp hq], hC⟩

private theorem Linked.mergeDirs {t : ℚ} {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l) :
    Linked P b lam t (mergeDirs l) := by
  induction l generalizing t with
  | nil => simp [LSPath.mergeDirs]
  | cons p l ih =>
    rw [mergeDirs_cons]
    have hrest := ih (linked_cons_iff.mp hl).2
    by_cases hp : p.2 = 0
    · rw [consMergeDir_of_eq_zero hp]
      simpa [hp] using hrest
    have hhead := exists_isAChain_head?_mergeDirs (linked_cons_iff.mp hl).2
      (linked_cons_iff.mp hl).1
    rcases hL : LSPath.mergeDirs l with _ | ⟨r, l'⟩
    · simp [consMergeDir, hp]
    · rw [hL] at hrest hhead
      by_cases hpr : p.1 = r.1
      · simp only [consMergeDir, hp, hpr, ↓reduceIte]
        cases l' with
        | nil => simp
        | cons s l' =>
          rw [linked_cons_cons] at hrest ⊢
          simpa [add_assoc] using hrest
      · simp only [consMergeDir, hp, hpr, ↓reduceIte]
        exact linked_cons_cons.mpr ⟨hhead r rfl, hrest⟩

/-! ### Lakshmibai–Seshadri paths from linked lists -/

/-- The directions of an LS path with the durations of their segments,
`[(τ₀, a₁ - a₀), …, (τ_l, a_{l+1} - a_l)]`. -/
def dirDurations (π : LSPath P b lam) : List (P.weylGroup × ℚ) :=
  List.ofFn fun j ↦ ((π.dir j).1, π.duration j)

@[simp]
theorem length_dirDurations (π : LSPath P b lam) : π.dirDurations.length = π.length + 1 := by
  simp [dirDurations]

@[simp]
theorem getElem_dirDurations (π : LSPath P b lam) (k : ℕ) (hk : k < π.dirDurations.length) :
    π.dirDurations[k] = ((π.dir ⟨k, by simpa using hk⟩).1, π.duration ⟨k, by simpa using hk⟩) := by
  simp only [dirDurations, List.getElem_ofFn]

/-- The directions of an LS path are minimal coset representatives. -/
theorem isMinimalCosetRep_of_mem_dirDurations (π : LSPath P b lam) {p : P.weylGroup × ℚ}
    (hp : p ∈ π.dirDurations) :
    (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact (π.dir j).2

/-- The segments of an LS path have positive durations. -/
theorem pos_of_mem_dirDurations (π : LSPath P b lam) {p : P.weylGroup × ℚ}
    (hp : p ∈ π.dirDurations) : 0 < p.2 := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact π.duration_pos j

/-- The total duration of the first `k` segments of an LS path is its `k`-th break time `a_k`. -/
theorem sum_map_snd_take_dirDurations (π : LSPath P b lam) (k : ℕ) (hk : k < π.length + 2) :
    ((π.dirDurations.take k).map Prod.snd).sum = π.time ⟨k, hk⟩ := by
  induction k with
  | zero => simpa using π.time_zero.symm
  | succ k ih =>
    rw [List.take_succ_eq_append_getElem (by simp; omega), List.map_append, List.sum_append,
      ih (by omega)]
    simp [duration_def]

/-- The durations of the segments of an LS path add up to `1`. -/
@[simp]
theorem sum_map_snd_dirDurations (π : LSPath P b lam) : (π.dirDurations.map Prod.snd).sum = 1 := by
  simp only [dirDurations, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  exact π.sum_duration

/-- The directions and durations of an LS path form a linked list starting at time `0`. -/
theorem linked_dirDurations (π : LSPath P b lam) : Linked P b lam 0 π.dirDurations := by
  refine linked_iff_getElem.mpr fun k hk ↦ ?_
  obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain ⟨k, by simpa using hk⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hhead
  · simpa using congrArg Subtype.val hlast
  · rw [zero_add, sum_map_snd_take_dirDurations _ _ (by simp at hk; omega)]
    simpa using hC

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The segments of the distinguished presentation of an LS path are those of its directions and
durations. -/
theorem map_snd_timed (π : LSPath P b lam) (f : M →+ V) :
    (π.timed 𝕜 f).map Prod.snd = π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam) := by
  simp [timed_def, dirDurations, List.map_ofFn, Function.comp_def]

/-- The LS path presented by a linked list `[(τ₀, d₀), …, (τ_l, d_l)]`, starting at time `0`, of
minimal coset representatives with nonnegative durations adding up to `1`. Its directions are
those of the list, with the entries of duration `0` dropped and consecutive repeated directions
merged; it presents the same piecewise-linear path (`TauCeti.LSPath.toPLPath_ofLinked`). -/
noncomputable def ofLinked (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l) :
    LSPath P b lam :=
  have hpos := length_mergeDirs_pos hsum
  { length := (mergeDirs l).length - 1
    dir j := ⟨((mergeDirs l)[j.1]'(by omega)).1, by
      obtain ⟨p, hp, hpq⟩ := exists_mem_of_mem_mergeDirs
        (List.getElem_mem (l := mergeDirs l) (n := j) (by omega))
      rw [← hpq]
      exact hmin p hp⟩
    time k := (((mergeDirs l).take k).map Prod.snd).sum
    time_zero := by simp
    time_last := by
      rw [Fin.val_last, Nat.sub_add_cancel hpos, List.take_length, sum_map_snd_mergeDirs, hsum]
    strictMono_time := Fin.strictMono_iff_lt_succ.mpr fun k ↦ by
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append]
      simpa using pos_of_mem_mergeDirs hnonneg (List.getElem_mem (by omega))
    dir_succ_ne j h := by
      have := List.isChain_iff_getElem.mp (isChain_mergeDirs l) j (by omega)
      exact this (congrArg Subtype.val h).symm
    exists_isAChain j := by
      obtain ⟨C, hhead, hlast, hC⟩ := linked_iff_getElem.mp hl.mergeDirs j (by omega)
      exact ⟨C, Subtype.ext hhead, Subtype.ext hlast, by simpa using hC⟩ }

private theorem length_ofLinked (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l) :
    (ofLinked l hmin hnonneg hsum hl).length + 1 = (mergeDirs l).length :=
  Nat.sub_add_cancel (length_mergeDirs_pos hsum)

private theorem time_ofLinked (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l)
    (k : Fin ((ofLinked l hmin hnonneg hsum hl).length + 2)) :
    (ofLinked l hmin hnonneg hsum hl).time k = (((mergeDirs l).take k).map Prod.snd).sum :=
  rfl

private theorem dir_ofLinked (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l)
    (j : Fin ((ofLinked l hmin hnonneg hsum hl).length + 1)) :
    ((ofLinked l hmin hnonneg hsum hl).dir j).1 =
      ((mergeDirs l)[j.1]'(by rw [← length_ofLinked l hmin hnonneg hsum hl]; exact j.2)).1 :=
  rfl

/-- The directions and durations of `TauCeti.LSPath.ofLinked l` are those of `l` after merging. -/
private theorem dirDurations_ofLinked_eq_mergeDirs (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l) :
    (ofLinked l hmin hnonneg hsum hl).dirDurations = mergeDirs l := by
  refine List.ext_getElem (by rw [length_dirDurations, length_ofLinked]) fun k hk₁ hk₂ ↦ ?_
  rw [getElem_dirDurations, duration_def, time_ofLinked, time_ofLinked, dir_ofLinked]
  refine Prod.ext rfl ?_
  rw [Fin.val_succ, Fin.val_castSucc, List.take_succ_eq_append_getElem hk₂, List.map_append,
    List.sum_append]
  simp

/-- An LS path is determined by its directions and durations. -/
theorem dirDurations_injective :
    Function.Injective (dirDurations : LSPath P b lam → List (P.weylGroup × ℚ)) := by
  intro π π' h
  have hlen : π.length = π'.length := by simpa using congrArg List.length h
  have hget : ∀ k (hk : k < π.length + 1), π.dirDurations[k]'(by simpa using hk) =
      π'.dirDurations[k]'(by simpa [← hlen] using hk) := fun k hk ↦ by simp only [h]
  refine ext (List.ext_getElem (by simp [hlen]) fun k hk₁ hk₂ ↦ ?_)
    (List.ext_getElem (by simp [hlen]) fun k hk₁ hk₂ ↦ ?_)
  · simp only [List.getElem_ofFn]
    exact Subtype.ext (by simpa using congrArg Prod.fst (hget k (by simpa using hk₁)))
  · simp only [List.getElem_ofFn]
    rw [← sum_map_snd_take_dirDurations π k (by simp at hk₁; omega),
      ← sum_map_snd_take_dirDurations π' k (by simp at hk₂; omega), h]

/-- The directions and durations of the LS path of a linked list with positive durations and
distinct consecutive directions are those of the list. -/
theorem dirDurations_ofLinked (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l)
    (hpos : ∀ p ∈ l, 0 < p.2) (hne : l.IsChain fun p q ↦ p.1 ≠ q.1) :
    (ofLinked l hmin hnonneg hsum hl).dirDurations = l := by
  rw [dirDurations_ofLinked_eq_mergeDirs, mergeDirs_eq_self hpos hne]

/-- An LS path is the LS path of its directions and durations. -/
@[simp]
theorem ofLinked_dirDurations (π : LSPath P b lam)
    (hmin : ∀ p ∈ π.dirDurations,
      (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ π.dirDurations, 0 ≤ p.2) (hsum : (π.dirDurations.map Prod.snd).sum = 1)
    (hl : Linked P b lam 0 π.dirDurations) : ofLinked π.dirDurations hmin hnonneg hsum hl = π := by
  refine dirDurations_injective (dirDurations_ofLinked _ _ _ _ _
    (fun _ hp ↦ π.pos_of_mem_dirDurations hp) (List.isChain_iff_getElem.mpr fun k hk ↦ ?_))
  simpa using fun h ↦ π.dir_succ_ne ⟨k, by simpa using hk⟩ (Subtype.ext h.symm)

/-- The path of `TauCeti.LSPath.ofLinked l` is presented by the segments `d • τ λ` of the list. -/
theorem toPLPath_ofLinked (f : M →+ V) (l : List (P.weylGroup × ℚ))
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (hnonneg : ∀ p ∈ l, 0 ≤ p.2) (hsum : (l.map Prod.snd).sum = 1) (hl : Linked P b lam 0 l) :
    (ofLinked l hmin hnonneg hsum hl).toPLPath 𝕜 f =
      PLPath.ofSegments 𝕜 (l.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) := by
  rw [toPLPath_def, map_snd_timed, dirDurations_ofLinked_eq_mergeDirs,
    ofSegments_map_mergeDirs f hnonneg]

end TauCeti.LSPath
