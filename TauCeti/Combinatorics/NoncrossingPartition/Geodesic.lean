/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.FormPerm
public import TauCeti.GroupTheory.Perm.SwapFactors
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# Noncrossing partitions are the geodesics to the full cycle

Write `#σ` for the number of cycles of a permutation `σ` of a finite type `α`, fixed points
included, so that `|σ| = Nat.card α - #σ` is its transposition length, the least number of
transpositions with product `σ`. For the cycle `γ` through the points of a finite set `s` in
increasing order, the triangle inequality `|γ| ≤ |σ| + |σ⁻¹ * γ|` reads
`#σ + #(σ⁻¹ * γ) ≤ #γ + Nat.card α`
(`Equiv.Perm.orbitCount_mul_add_orbitCount_le_orbitCount_add_card`), and `σ` lies on a geodesic
from `1` to `γ` when equality holds.

The permutation `p_π` of a noncrossing partition `π` of `s`, which cycles each part in increasing
order, lies on such a geodesic: its complement `p_π⁻¹ * γ` is the permutation of the Kreweras
complement of `π` (`Finpartition.IsNoncrossing.formPerm_kreweras`), and on `Fin n` the two
cycle counts add up to `n + 1`. This file proves the converse: a geodesic permutation supported on
`s` is the permutation of a noncrossing partition of `s`, which is unique by
`Finpartition.formPerm_injective`. On `Fin n` with `n ≠ 0`, where `γ = finRotate n`, a
permutation `σ` therefore satisfies `#σ + #(σ⁻¹ * finRotate n) = n + 1` if and only if `σ = p_π`
for a noncrossing partition `π`.

The converse is proved by induction on `s`, removing its largest point `m`: the geodesic condition
for `σ` forces the predecessor of `m` in its cycle to lie, in the Kreweras complement of the
partition obtained by deleting `m`, in the part of the largest remaining point, which is where `m`
can be reinserted without creating a crossing.

## Main results

* `Finpartition.exists_isNoncrossing_formPerm_eq`: a permutation supported on `s` that lies on a
  geodesic from `1` to the cycle through `s` is the permutation of a noncrossing partition of `s`.
* `TauCeti.NoncrossingPartition.orbitCount_add_orbitCount_inv_mul_finRotate_eq_iff`: for `n ≠ 0`,
  a permutation `σ` of `Fin n` satisfies `#σ + #(σ⁻¹ * finRotate n) = n + 1` exactly when it is the
  permutation of a noncrossing partition of `Fin n`.

## References

* P. Biane, *Some properties of crossings and partitions*, Discrete Math. 175 (1997), 41–53.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 23.
-/

public section

open Equiv Equiv.Perm Finset TauCeti

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- A permutation whose cycles are traversed in increasing cyclic order, each point moving to the
next point of its cycle or from the last point back to the first, and whose cycles do not cross.
These are exactly the permutations of noncrossing partitions. -/
private def IsNoncrossingPerm (σ : Perm α) : Prop :=
  (∀ x w, σ.SameCycle x w → (x < σ x → x < w → σ x ≤ w) ∧ (σ x ≤ x → σ x ≤ w ∧ w ≤ x)) ∧
    ∀ a b c d, σ.SameCycle a c → σ.SameCycle b d → a < b → b < c → c < d → σ.SameCycle a b

private theorem isNoncrossingPerm_one : IsNoncrossingPerm (1 : Perm α) := by
  refine ⟨fun x w hxw => ?_, fun a b c d hac _ hab hbc _ => ?_⟩
  · obtain rfl := sameCycle_one.1 hxw
    simp
  · exact absurd (sameCycle_one.1 hac) (hab.trans hbc).ne

/-- The permutation of a noncrossing partition has increasing, noncrossing cycles. -/
private theorem IsNoncrossing.isNoncrossingPerm_formPerm {P : Finpartition s}
    (hP : P.IsNoncrossing) : IsNoncrossingPerm P.formPerm := by
  have hmem {x y : α} (hxy : x ≠ y) (h : P.formPerm.SameCycle x y) : x ∈ s := by
    by_contra hx
    exact hxy (h.eq_of_left (P.formPerm_apply_of_notMem hx))
  refine ⟨fun x w hxw => ?_, fun a b c d hac hbd hab hbc hcd => ?_⟩
  · by_cases hx : x ∈ s
    · have hw := (P.sameCycle_formPerm_iff hx).1 hxw
      obtain ⟨-, h₁, h₂⟩ := (P.formPerm_apply_eq_iff hx).1 rfl
      exact ⟨fun h hlt => h₁ h w hw hlt, fun h => h₂ h w hw⟩
    · have hfix := P.formPerm_apply_of_notMem hx
      obtain rfl := hxw.eq_of_left hfix
      simp [hfix]
  · have has := hmem (hab.trans hbc).ne hac
    have hbs := hmem (hbc.trans hcd).ne hbd
    rw [P.sameCycle_formPerm_iff has] at hac ⊢
    rw [P.sameCycle_formPerm_iff hbs] at hbd
    rw [isNoncrossing_iff_part.1 hP a has b hbs c hac d hbd hab hbc hcd]
    exact P.mem_part hbs

/-- A permutation supported on `s` with increasing, noncrossing cycles is the permutation of the
noncrossing partition of `s` into its cycles. -/
private theorem exists_isNoncrossing_formPerm_eq_of_isNoncrossingPerm {σ : Perm α}
    (hσ : ∀ x ∉ s, σ x = x) (hσnc : IsNoncrossingPerm σ) :
    ∃ P : Finpartition s, P.IsNoncrossing ∧ P.formPerm = σ := by
  classical
  obtain ⟨hinc, hnc⟩ := hσnc
  have hmem {x w : α} (hx : x ∈ s) (hxw : σ.SameCycle x w) : w ∈ s := by
    by_contra hw
    exact hw (hxw.eq_of_right (hσ w hw) ▸ hx)
  let P := ofSetSetoid (SameCycle.setoid σ) s
  have hpart {x w : α} (hx : x ∈ s) : w ∈ P.part x ↔ σ.SameCycle x w := by
    rw [mem_part_ofSetSetoid_iff_rel]
    exact ⟨fun h => h.2.2, fun h => ⟨hx, hmem hx h, h⟩⟩
  refine ⟨P, isNoncrossing_iff_part.2 fun a ha b hb c hc d hd hab hbc hcd => ?_, ?_⟩
  · rw [hpart ha] at hc
    rw [hpart hb] at hd
    exact ((P.mem_part_iff_part_eq_part hb ha).1 ((hpart ha).2
      (hnc a b c d hc hd hab hbc hcd))).symm
  · ext x
    by_cases hx : x ∈ s
    · refine (P.formPerm_apply_eq_iff hx).2 ⟨(hpart hx).2 (sameCycle_apply_right.2
        (SameCycle.refl σ x)), fun h w hw hlt => ?_, fun h w hw => ?_⟩
      exacts [(hinc x w ((hpart hx).1 hw)).1 h hlt, (hinc x w ((hpart hx).1 hw)).2 h]
    · rw [P.formPerm_apply_of_notMem hx, hσ x hx]

/-- Removing a point `m` from its cycle `σ p = m` by `σ' = σ * swap p m` only splits cycles: every
cycle of `σ'` lies in a cycle of `σ`. -/
private theorem sameCycle_of_sameCycle_mul_swap {σ σ' : Perm α} {p m u v : α}
    (hσp : σ p = m) (hσ' : σ' = σ * swap p m) (hσ'm : σ' m = m) (h : σ'.SameCycle u v) :
    σ.SameCycle u v := by
  refine SameCycle.of_forall_sameCycle_apply (fun x => ?_) h
  by_cases hxp : x = p
  · rw [hxp, hσ', mul_apply, swap_apply_left]
    exact (sameCycle_apply_right.2 (SameCycle.refl σ p)).trans (by
      rw [hσp]; exact sameCycle_apply_right.2 (SameCycle.refl σ m))
  by_cases hxm : x = m
  · rw [hxm, hσ'm]
  · rw [hσ', mul_apply, swap_apply_of_ne_of_ne hxp hxm]
    exact sameCycle_apply_right.2 (SameCycle.refl σ x)

/-- Conversely, collapsing `m` onto `p` (`f m = p`, and `f` the identity elsewhere) maps each
cycle of `σ` into a cycle of `σ' = σ * swap p m`, when `m` is not fixed by `σ` and `σ p = m`. -/
private theorem sameCycle_collapse_of_mul_swap {σ σ' : Perm α} {p m : α} {f : α → α}
    (hσp : σ p = m) (hpm : p ≠ m) (hσm : σ m ≠ m) (hσ' : σ' = σ * swap p m)
    (hfm : f m = p) (hf : ∀ {x}, x ≠ m → f x = x) {x y : α} (h : σ.SameCycle x y) :
    σ'.SameCycle (f x) (f y) := by
  have hσ'p : σ' p = σ m := by rw [hσ', mul_apply, swap_apply_left]
  refine h.map_of_forall_sameCycle_apply fun x => ?_
  by_cases hxm : x = m
  · rw [hxm, hfm, hf hσm, ← hσ'p]
    exact sameCycle_apply_right.2 (SameCycle.refl σ' p)
  by_cases hxp : x = p
  · rw [hxp, hσp, hfm, hf hpm]
  · have hσx : σ x ≠ m := fun h => hxp (σ.injective (h.trans hσp.symm))
    rw [hf hxm, hf hσx, ← show σ' x = σ x by
      rw [hσ', mul_apply, swap_apply_of_ne_of_ne hxp hxm]]
    exact sameCycle_apply_right.2 (SameCycle.refl σ' x)

/-- The increasing-order half of the reinsertion of a largest point `m` after `p = σ⁻¹ m`; see
`isNoncrossingPerm_of_isNoncrossingPerm_mul_swap`. -/
private theorem increasing_of_mul_swap {σ σ' : Perm α} {p m : α} {f : α → α}
    (hσp : σ p = m) (hpm' : p < m) (hσm : σ m ≠ m) (hσ'p : σ' p = σ m)
    (hσ'x : ∀ {x}, x ≠ p → x ≠ m → σ' x = σ x) (hfm : f m = p) (hf : ∀ {x}, x ≠ m → f x = x)
    (hσσ' : ∀ {x y}, σ.SameCycle x y → σ'.SameCycle (f x) (f y))
    (hmoved : ∀ {x w}, σ.SameCycle x w → x ≠ w → w ≤ m) (hle : ∀ x, σ x ≠ x → x ≤ m)
    (hinc' : ∀ x w, σ'.SameCycle x w →
      (x < σ' x → x < w → σ' x ≤ w) ∧ (σ' x ≤ x → σ' x ≤ w ∧ w ≤ x))
    (hK : ∀ u v, σ'.SameCycle u v → p < u → p < v) (hσm_le : σ m ≤ p) (x w : α)
    (hxw : σ.SameCycle x w) :
    (x < σ x → x < w → σ x ≤ w) ∧ (σ x ≤ x → σ x ≤ w ∧ w ≤ x) := by
  have hpm : p ≠ m := hpm'.ne
  by_cases hxm : x = m
  · -- The point `m` moves down to the first point of the cycle of `p` in `σ'`.
    rw [hxm] at hxw ⊢
    have hlt : σ m < m := (hle _ fun h => hσm (σ.injective h)).lt_of_ne hσm
    refine ⟨fun h => absurd h (not_lt.2 hlt.le), fun _ => ?_⟩
    by_cases hwm : w = m
    · rw [hwm]
      exact ⟨hlt.le, le_rfl⟩
    have hpw := hσσ' hxw
    rw [hfm, hf hwm] at hpw
    have h := (hinc' p w hpw).2 (by rw [hσ'p]; exact hσm_le)
    rw [hσ'p] at h
    exact ⟨h.1, hmoved hxw fun h => hwm h.symm⟩
  by_cases hxp : x = p
  · -- The point `p` moves up to `m`, and its cycle has no point between `p` and `m`.
    rw [hxp] at hxw ⊢
    rw [hσp]
    refine ⟨fun _ hpw => ?_, fun h => absurd h (not_le.2 hpm')⟩
    by_cases hwm : w = m
    · rw [hwm]
    have h := hσσ' hxw
    rw [hf hpm, hf hwm] at h
    exact absurd (hK w p h.symm hpw) (lt_irrefl p)
  · -- Elsewhere `σ` agrees with `σ'`, and `m` lies above the cycle through `x`.
    rw [← hσ'x hxp hxm]
    have hxw' := hσσ' hxw
    rw [hf hxm] at hxw'
    by_cases hwm : w = m
    · rw [hwm] at hxw hxw' ⊢
      rw [hfm] at hxw'
      refine ⟨fun _ _ => ?_, fun h => ?_⟩
      · rw [hσ'x hxp hxm]
        by_cases hσxm : σ x = m
        · exact hσxm.le
        · exact hmoved ((sameCycle_apply_left.2 hxw).symm) fun h => hσxm h.symm
      · have hpx := ((hinc' x p hxw').2 h).2
        exact absurd (hK x p hxw' (hpx.lt_of_ne fun h => hxp h.symm)) (lt_irrefl p)
    · rw [hf hwm] at hxw'
      exact hinc' x w hxw'

/-- The noncrossing half of the reinsertion of a largest point `m` after `p = σ⁻¹ m`; see
`isNoncrossingPerm_of_isNoncrossingPerm_mul_swap`. A crossing through `m` would be a crossing
through `p`, or would leave the points above `p`. -/
private theorem noncrossing_of_mul_swap {σ σ' : Perm α} {p m : α} {f : α → α}
    (hfm : f m = p) (hf : ∀ {x}, x ≠ m → f x = x)
    (hmoved : ∀ {x w}, σ.SameCycle x w → x ≠ w → w ≤ m)
    (hσ'σ : ∀ {u v}, σ'.SameCycle u v → σ.SameCycle u v)
    (hσσ' : ∀ {x y}, σ.SameCycle x y → σ'.SameCycle (f x) (f y))
    (hnc' : ∀ a b c d, σ'.SameCycle a c → σ'.SameCycle b d → a < b → b < c → c < d →
      σ'.SameCycle a b)
    (hK : ∀ u v, σ'.SameCycle u v → p < u → p < v) (a b c d : α)
    (hac : σ.SameCycle a c) (hbd : σ.SameCycle b d) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    σ.SameCycle a b := by
  have hdm : d ≤ m := hmoved hbd (hbc.trans hcd).ne
  have hcm : c ≠ m := (hcd.trans_le hdm).ne
  have hbm : b ≠ m := ((hbc.trans hcd).trans_le hdm).ne
  have ham : a ≠ m := ((hab.trans hbc).trans (hcd.trans_le hdm)).ne
  have hac' := hσσ' hac
  rw [hf ham, hf hcm] at hac'
  refine hσ'σ ?_
  by_cases hdm' : d = m
  · have hbp := hσσ' hbd
    rw [hf hbm, hdm', hfm] at hbp
    rcases lt_trichotomy c p with hcp | rfl | hpc
    · exact hnc' a b c p hac' hbp hab hbc hcp
    · exact hac'.trans hbp.symm
    · exact absurd (hK b p hbp ((hK c a hac'.symm hpc).trans hab)) (lt_irrefl p)
  · have hbd' := hσσ' hbd
    rw [hf hbm, hf hdm'] at hbd'
    exact hnc' a b c d hac' hbd' hab hbc hcd

/-- **Reinserting a largest point.** Let `σ` move only points `x ≤ m`, with `σ m ≠ m`, and let
`p = σ⁻¹ m`. If removing `m` from its cycle gives a permutation `σ' = σ * swap p m` with increasing
noncrossing cycles, and the points above `p` form a union of cycles of `σ'`, then `σ` has
increasing noncrossing cycles: it inserts `m` after the last point `p` of its cycle. -/
private theorem isNoncrossingPerm_of_isNoncrossingPerm_mul_swap {σ σ' : Perm α} {p m : α}
    (hσp : σ p = m) (hpm : p ≠ m) (hσm : σ m ≠ m) (hσ' : σ' = σ * swap p m) (hσ'm : σ' m = m)
    (hle : ∀ x, σ x ≠ x → x ≤ m)
    (hσ'nc : IsNoncrossingPerm σ') (hK : ∀ u v, σ'.SameCycle u v → p < u → p < v) :
    IsNoncrossingPerm σ := by
  -- After comparing the cycles of `σ` and `σ'`, the increasing order is checked at `m`, at `p`
  -- and elsewhere, and then a crossing is ruled out according to whether it passes through `m`.
  obtain ⟨hinc', hnc'⟩ := hσ'nc
  have hσ'p : σ' p = σ m := by rw [hσ', mul_apply, swap_apply_left]
  have hσ'x {x : α} (hxp : x ≠ p) (hxm : x ≠ m) : σ' x = σ x := by
    rw [hσ', mul_apply, swap_apply_of_ne_of_ne hxp hxm]
  have hmoved {x w : α} (h : σ.SameCycle x w) (hxw : x ≠ w) : w ≤ m :=
    hle w fun hw => hxw (h.eq_of_right hw)
  have hpm' : p < m := (hle p (by rw [hσp]; exact hpm.symm)).lt_of_ne hpm
  let f : α → α := fun x => if x = m then p else x
  have hfm : f m = p := by simp [f]
  have hf {x : α} (hxm : x ≠ m) : f x = x := by simp [f, hxm]
  have hσσ' {x y : α} (h : σ.SameCycle x y) : σ'.SameCycle (f x) (f y) :=
    sameCycle_collapse_of_mul_swap hσp hpm hσm hσ' hfm hf h
  -- `p` is the last point of its cycle in `σ'`, so `σ' p = σ m` is the first.
  have hσm_le : σ m ≤ p := by
    have h : σ'.SameCycle p (σ m) := by
      rw [← hσ'p]; exact sameCycle_apply_right.2 (SameCycle.refl σ' p)
    exact not_lt.1 fun hlt => lt_irrefl p (hK _ _ h.symm hlt)
  exact ⟨fun x w hxw => increasing_of_mul_swap hσp hpm' hσm hσ'p hσ'x hfm hf hσσ' hmoved hle
      hinc' hK hσm_le x w hxw,
    fun a b c d hac hbd hab hbc hcd => noncrossing_of_mul_swap hfm hf hmoved
      (sameCycle_of_sameCycle_mul_swap hσp hσ' hσ'm) hσσ' hnc' hK a b c d hac hbd hab hbc hcd⟩

/-- If `p` and the largest point `m'` of `t` lie in one cycle of `p_P⁻¹ * γ`, that is, the bars
after them lie in one part of the Kreweras complement of the noncrossing partition `P`, then the
points above `p` form a union of cycles of `p_P`. -/
private theorem IsNoncrossing.lt_of_sameCycle_of_sameCycle {t : Finset α} {P : Finpartition t}
    (hP : P.IsNoncrossing) {p m' u v : α} (hpt : p ∈ t) (hm' : ∀ x ∈ t, x ≤ m')
    (h : (P.formPerm⁻¹ * (⊤ : Finpartition t).formPerm).SameCycle p m')
    (huv : P.formPerm.SameCycle u v) (hpu : p < u) : p < v := by
  by_cases hut : u ∈ t
  swap
  · rwa [← huv.eq_of_left (P.formPerm_apply_of_notMem hut)]
  rw [← hP.formPerm_kreweras, P.kreweras.sameCycle_formPerm_iff hpt] at h
  obtain ⟨-, -, hI⟩ := mem_part_kreweras_iff.1 h
  rw [P.sameCycle_formPerm_iff hut] at huv
  rcases Set.mem_uIoc.1 (hI u v huv (Set.mem_uIoc.2 (Or.inl ⟨hpu, hm' u hut⟩))) with h | h
  · exact h.1
  · exact absurd h.1 (not_lt.2 (h.2.trans (hpu.le.trans (hm' u hut))))

/-- **Removing a largest point keeps a permutation geodesic.** Let `γ` and `γ'` be the cycles
through `insert m t` and `t`, so that `γ = γ' * swap m' m` and `#γ + 1 = #γ'`, and let `σ` be
geodesic for `γ` with `σ p = m ≠ p`, that is, `σ' = σ * swap p m` fixes `m`. Then `σ'`, which
removes `m` from its cycle, is geodesic for `γ'`, and `p` lies in the cycle of `m'` in
`σ'⁻¹ * γ'`. -/
private theorem orbitCount_add_orbitCount_mul_swap_eq [Finite α] {t : Finset α}
    {σ σ' : Perm α} {p m m' : α}
    (hγ : (⊤ : Finpartition (insert m t)).formPerm = (⊤ : Finpartition t).formPerm * swap m' m)
    (hcγ : orbitCount (⊤ : Finpartition (insert m t)).formPerm + 1 =
      orbitCount (⊤ : Finpartition t).formPerm)
    (hmt : m ∉ t) (hm'm : m' ≠ m) (hpm : p ≠ m) (hσ' : σ' = σ * swap p m) (hσ'm : σ' m = m)
    (h : orbitCount σ + orbitCount (σ⁻¹ * (⊤ : Finpartition (insert m t)).formPerm) =
      orbitCount (⊤ : Finpartition (insert m t)).formPerm + Nat.card α) :
    orbitCount σ' + orbitCount (σ'⁻¹ * (⊤ : Finpartition t).formPerm) =
        orbitCount (⊤ : Finpartition t).formPerm + Nat.card α ∧
      (σ'⁻¹ * (⊤ : Finpartition t).formPerm).SameCycle p m' := by
  have hγm : (⊤ : Finpartition t).formPerm m = m := formPerm_apply_of_notMem _ hmt
  have hσσ' : σ' * swap p m = σ := by rw [hσ', mul_assoc, swap_mul_self, mul_one]
  have hXm : (σ'⁻¹ * (⊤ : Finpartition t).formPerm) m = m := by
    rw [mul_apply, hγm, Perm.inv_eq_iff_eq, hσ'm]
  -- Each of `σ` and `σ⁻¹ * γ` differs from its counterpart by one transposition, as `γ` does.
  have hc₁ : orbitCount σ + 1 = orbitCount σ' := by
    rw [← hσσ']
    exact orbitCount_mul_swap_add_one_of_not_sameCycle fun hc => hpm (hc.eq_of_right hσ'm)
  have hcZ : orbitCount (σ'⁻¹ * (⊤ : Finpartition t).formPerm * swap m' m) + 1 =
      orbitCount (σ'⁻¹ * (⊤ : Finpartition t).formPerm) :=
    orbitCount_mul_swap_add_one_of_not_sameCycle fun hc => hm'm (hc.eq_of_right hXm)
  have hrel : orbitCount (σ⁻¹ * (⊤ : Finpartition (insert m t)).formPerm) =
      orbitCount (σ'⁻¹ * (⊤ : Finpartition t).formPerm * swap m' m * swap p m) := by
    rw [hγ, ← hσσ', mul_inv_rev, swap_inv, mul_assoc, orbitCount_mul_comm]
    simp only [mul_assoc]
  have htri : orbitCount σ' + orbitCount (σ'⁻¹ * (⊤ : Finpartition t).formPerm) ≤
      orbitCount (⊤ : Finpartition t).formPerm + Nat.card α := by
    have h := orbitCount_mul_add_orbitCount_le_orbitCount_add_card (⊤ : Finpartition t).formPerm
      ((⊤ : Finpartition t).formPerm⁻¹ * σ')
    rwa [mul_inv_cancel_left, ← orbitCount_inv ((⊤ : Finpartition t).formPerm⁻¹ * σ'),
      mul_inv_rev, inv_inv] at h
  -- Merging the cycles of `p` and `m` would overshoot the triangle inequality, so they split.
  have hsplit : (σ'⁻¹ * (⊤ : Finpartition t).formPerm * swap m' m).SameCycle p m := by
    by_contra hns
    have := orbitCount_mul_swap_add_one_of_not_sameCycle hns
    omega
  have hcs := orbitCount_mul_swap_of_sameCycle hpm hsplit
  refine ⟨by omega, ?_⟩
  by_cases hpm' : p = m'
  · rw [hpm']
  have h := (sameCycle_mul_comm_iff (swap m' m) _).1 hsplit
  rw [swap_apply_of_ne_of_ne hpm' hpm, swap_apply_right] at h
  rcases h.sameCycle_or_of_swap_mul with h | ⟨h | h, -⟩
  · exact h
  · exact h
  · exact absurd (h.eq_of_right hXm) hpm

/-- A permutation that fixes every point except possibly `m` is the identity. -/
private theorem eq_one_of_forall_ne_apply_eq {σ : Perm α} {m : α} (hσ : ∀ x, x ≠ m → σ x = x) :
    σ = 1 := by
  ext x
  rw [Perm.one_apply]
  by_contra hx
  have h₁ : x = m := by
    by_contra h
    exact hx (hσ x h)
  have h₂ : σ x = m := by
    by_contra h
    exact hx (σ.injective (hσ (σ x) h))
  exact hx (h₂.trans h₁.symm)

/-- **Geodesic permutations have increasing noncrossing cycles.** A permutation supported on `s`
with `#σ + #(σ⁻¹ * γ) = #γ + Nat.card α`, for the cycle `γ` through `s`, has increasing
noncrossing cycles. -/
private theorem isNoncrossingPerm_of_orbitCount_add_orbitCount_eq [Finite α] (s : Finset α)
    (σ : Perm α) (hσ : ∀ x ∉ s, σ x = x)
    (h : orbitCount σ + orbitCount (σ⁻¹ * (⊤ : Finpartition s).formPerm) =
      orbitCount (⊤ : Finpartition s).formPerm + Nat.card α) :
    IsNoncrossingPerm σ := by
  induction s using Finset.induction_on_max generalizing σ with
  | empty =>
    obtain rfl : σ = 1 := Equiv.ext fun x => hσ x (notMem_empty x)
    exact isNoncrossingPerm_one
  | insert m t hm ih =>
  have hmt : m ∉ t := fun h => (hm m h).false
  have hle : ∀ x, σ x ≠ x → x ≤ m := fun x hx => by
    by_contra hxm
    exact hx (hσ x (by
      simpa only [mem_insert, not_or] using ⟨fun h => hxm h.le, fun hxt => hxm (hm x hxt).le⟩))
  rcases t.eq_empty_or_nonempty with rfl | ht
  · -- A permutation moving at most the point `m` is the identity.
    obtain rfl := eq_one_of_forall_ne_apply_eq (m := m) fun x hx => hσ x (by simp [hx])
    exact isNoncrossingPerm_one
  -- The cycle through `insert m t` is the cycle through `t` with `m` inserted after `m'`.
  have hm' := t.max'_mem ht
  have hγ := formPerm_top_insert hm hm' fun x hx => t.le_max' x hx
  have hm'm : t.max' ht ≠ m := (hm _ hm').ne
  have hcγ := orbitCount_formPerm_top_insert_add_one hm hm' fun x hx => t.le_max' x hx
  by_cases hσm : σ m = m
  · -- If `σ` fixes `m`, it is a geodesic permutation supported on `t`.
    have hγm : (⊤ : Finpartition t).formPerm m = m := formPerm_apply_of_notMem _ hmt
    have hσt : ∀ x ∉ t, σ x = x := fun x hx => by
      by_cases hxm : x = m
      · rw [hxm, hσm]
      · exact hσ x (by simp [hxm, hx])
    have hfix : (σ⁻¹ * (⊤ : Finpartition t).formPerm) m = m := by
      rw [mul_apply, hγm, Perm.inv_eq_iff_eq, hσm]
    have hX : orbitCount (σ⁻¹ * (⊤ : Finpartition (insert m t)).formPerm) + 1 =
        orbitCount (σ⁻¹ * (⊤ : Finpartition t).formPerm) := by
      rw [hγ, ← mul_assoc]
      exact orbitCount_mul_swap_add_one_of_not_sameCycle fun hc => hm'm (hc.eq_of_right hfix)
    exact ih σ hσt (by omega)
  -- Otherwise remove `m` from its cycle: `σ'` sends the predecessor `p` of `m` to `σ m`.
  obtain ⟨p, hσp⟩ : ∃ p, σ p = m := ⟨σ⁻¹ m, by simp⟩
  have hpm : p ≠ m := fun h => hσm (by rw [← h] at hσp ⊢; rw [hσp, h])
  have hpt : p ∈ t := by
    by_contra hpt
    exact hpm ((hσ p (by simp [hpm, hpt])).symm.trans hσp)
  obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = σ * swap p m := ⟨_, rfl⟩
  have hσ'm : σ' m = m := by rw [hσ', mul_apply, swap_apply_right, hσp]
  have hσ't : ∀ x ∉ t, σ' x = x := fun x hx => by
    by_cases hxm : x = m
    · rw [hxm, hσ'm]
    · have hxp : x ≠ p := fun h => hx (h ▸ hpt)
      rw [hσ', mul_apply, swap_apply_of_ne_of_ne hxp hxm, hσ x (by simp [hxm, hx])]
  -- By induction `σ'` is the permutation of a noncrossing partition `P'` of `t`, and the points
  -- above `p` form a union of parts of `P'`, because of the Kreweras complement of `P'`.
  obtain ⟨hgeo, hpm'⟩ := orbitCount_add_orbitCount_mul_swap_eq hγ hcγ hmt hm'm hpm hσ' hσ'm h
  have hσ'nc := ih σ' hσ't hgeo
  obtain ⟨P', hP', rfl⟩ := exists_isNoncrossing_formPerm_eq_of_isNoncrossingPerm hσ't hσ'nc
  exact isNoncrossingPerm_of_isNoncrossingPerm_mul_swap hσp hpm hσm hσ' hσ'm hle hσ'nc
    fun _ _ huv hpu => hP'.lt_of_sameCycle_of_sameCycle hpt (fun x hx => t.le_max' x hx) hpm' huv
      hpu

/-- **Geodesic permutations are permutations of noncrossing partitions.** Let `γ` be the cycle
through the points of `s` in increasing order. A permutation `σ` supported on `s` that lies on a
geodesic from `1` to `γ`, in the sense that `#σ + #(σ⁻¹ * γ) = #γ + Nat.card α` where `#` counts
cycles including fixed points, is the permutation of a noncrossing partition of `s`. -/
theorem exists_isNoncrossing_formPerm_eq [Finite α] {σ : Perm α} (hσ : ∀ x ∉ s, σ x = x)
    (h : orbitCount σ + orbitCount (σ⁻¹ * (⊤ : Finpartition s).formPerm) =
      orbitCount (⊤ : Finpartition s).formPerm + Nat.card α) :
    ∃ P : Finpartition s, P.IsNoncrossing ∧ P.formPerm = σ :=
  exists_isNoncrossing_formPerm_eq_of_isNoncrossingPerm hσ
    (isNoncrossingPerm_of_orbitCount_add_orbitCount_eq s σ hσ h)

end Finpartition

namespace TauCeti.NoncrossingPartition

/-- **The geodesic characterization of noncrossing partitions.** For `n ≠ 0`, a permutation `σ`
of `Fin n` satisfies `#σ + #(σ⁻¹ * finRotate n) = n + 1`, where `#` counts cycles including fixed
points, exactly when it is the permutation of a noncrossing partition of `Fin n`. Equivalently,
the transposition lengths satisfy `|σ| + |σ⁻¹ * finRotate n| = n - 1 = |finRotate n|`. -/
theorem orbitCount_add_orbitCount_inv_mul_finRotate_eq_iff {n : ℕ} (hn : n ≠ 0)
    {σ : Perm (Fin n)} :
    orbitCount σ + orbitCount (σ⁻¹ * finRotate n) = n + 1 ↔
      ∃ π : NoncrossingPartition (univ : Finset (Fin n)),
        (π : Finpartition (univ : Finset (Fin n))).formPerm = σ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨P, hP, hPσ⟩ := Finpartition.exists_isNoncrossing_formPerm_eq (s := univ) (σ := σ)
      (fun x hx => absurd (mem_univ x) hx) (by
        rw [Finpartition.formPerm_top_eq_finRotate, orbitCount_finRotate,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        simp only [hn, ↓reduceIte]
        omega)
    exact ⟨⟨P, hP⟩, hPσ⟩
  · rintro ⟨π, rfl⟩
    exact orbitCount_formPerm_add_orbitCount_inv_mul_finRotate hn π

end TauCeti.NoncrossingPartition
