/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.Basic
public import TauCeti.ModelTheory.BackAndForth.Equivalence
import Mathlib.Data.Fintype.Card

/-!
# Back-and-forth equivalence for row assemblies

This file develops the back-and-forth calculus for row assemblies over a relational component
language `Lc`:

1. **Assembly along a row bijection.** Two tuples `a` and `b` in row assemblies over `R₁` and
   `R₂` are `MatchedAlong eR α a b` when corresponding entries occupy slots matched by
   `eR : R₁ ≃ R₂` and every finite subtuple landing in a single fiber `(r, τ)` is
   `BFEquiv`-equivalent at depth `α` to its partner in `(eR r, τ)` (including the empty subtuple,
   which compares nullary relations and unpopulated fibers). Such tuples are `BFEquiv`-equivalent
   at depth `α` in the assembled language (`MatchedAlong.bfEquiv`). In particular, if
   `eR : R₁ ≃ R₂` matches fibers at level `α`, then the empty tuples and any matching tuples
   of row markers are `BFEquiv`-equivalent at level `α`.
2. **Pointed fiber restriction.** If `a` and `b` are `BFEquiv`-equivalent at depth `α` and carry
   the row marker `.row r₁` at position `i₀` to `.row r₂`, then any subtuple lying in fiber
   `(r₁, τ)` is `BFEquiv`-equivalent at depth `α` to the corresponding subtuple in `(r₂, τ)`.
3. **Owner-row step.** Back-and-forth equivalence of `n`-tuples at depth `β + n` extends to
   equivalence at depth `β` after appending the owner row of every entry.

## Main definitions

* `TauCeti.RowAssembly.MatchedAlong`: fiberwise back-and-forth matching of assembly tuples along a
  fixed bijection of rows.

## Main results

* `TauCeti.RowAssembly.MatchedAlong.bfEquiv`: assembly of back-and-forth equivalence at the same
  level `α`.
* `TauCeti.RowAssembly.bfEquiv_elim0_of_rowEquiv` and
  `TauCeti.RowAssembly.bfEquiv_rows_of_rowEquiv`: back-and-forth equivalence of empty tuples and
  row-marker tuples along a row bijection.
* `TauCeti.RowAssembly.bfEquiv_fiber_of_bfEquiv` and
  `TauCeti.RowAssembly.bfEquiv_fiber_elim0_of_bfEquiv_row`: pointed restriction of back-and-forth
  equivalence to a fiber.
* `TauCeti.RowAssembly.bfEquiv_append_ownerRow` and
  `TauCeti.RowAssembly.bfEquiv_ownerRow_of_bfEquiv_add`: appending owner rows at the cost of `n`
  back-and-forth levels.

## References

Adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/ModelTheory/FiberBFAssembly.lean`,
`InfinitaryLogic/ModelTheory/FiberBFRestriction.lean`, and
`InfinitaryLogic/ModelTheory/FiberOwnerRows.lean` (checkpoint
`518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0).
-/

public section

universe u u' v' w₁ w₂ w₁' w₂' o

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Fin

variable {U : Type u} {Lc : Language.{u', v'}}
variable {R₁ : Type w₁} {R₂ : Type w₂}
variable {C₁ : R₁ → Label U → Type w₁'} {C₂ : R₂ → Label U → Type w₂'}
variable [∀ r τ, Lc.Structure (C₁ r τ)] [∀ r τ, Lc.Structure (C₂ r τ)]

/-! ### Back-and-forth assembly along a row bijection -/

section Assembly

variable [Lc.IsRelational]

/-- Two tuples in row assemblies are matched at depth `α` along a bijection `eR : R₁ ≃ R₂`
when corresponding entries occupy corresponding slots and every finite subtuple landing in a single
fiber `(r, τ)` is `BFEquiv`-equivalent at depth `α` to its partner in `(eR r, τ)`. -/
structure MatchedAlong (eR : R₁ ≃ R₂) (α : Ordinal.{o}) {n : ℕ}
    (a : Fin n → Carrier R₁ C₁) (b : Fin n → Carrier R₂ C₂) : Prop where
  /-- Corresponding entries occupy slots matched by `eR`. -/
  slot_eq : ∀ i, (b i).slot = (a i).slot.map eR (Prod.map eR id)
  /-- Every finite subtuple in a single fiber `(r, τ)` matches its partner at depth `α`. -/
  fiber_bfEquiv : ∀ (r : R₁) (τ : Label U) (m : ℕ) (idx : Fin m → Fin n)
    (x : Fin m → C₁ r τ) (y : Fin m → C₂ (eR r) τ),
    (∀ j, a (idx j) = .pt r τ (x j)) →
    (∀ j, b (idx j) = .pt (eR r) τ (y j)) →
    BFEquiv (L := Lc) α m x y

namespace MatchedAlong

variable {eR : R₁ ≃ R₂} {α β : Ordinal.{o}} {n : ℕ}
variable {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}

/-- Fiberwise matching is symmetric along the inverse row bijection. -/
theorem symm (h : MatchedAlong (Lc := Lc) eR α a b) :
    MatchedAlong (Lc := Lc) eR.symm α b a where
  slot_eq i := by rw [h.slot_eq i]; rcases (a i).slot with r | ⟨r, τ⟩ <;> simp
  fiber_bfEquiv r₂ τ m idx y x hy hx := by
    generalize hr : eR.symm r₂ = r₁ at x hx
    obtain rfl : r₂ = eR r₁ := by rw [← hr, eR.apply_symm_apply]
    exact (h.fiber_bfEquiv r₁ τ m idx x y hx hy).symm

/-- Fiberwise matching descends to every lower back-and-forth level. -/
theorem mono (h : MatchedAlong (Lc := Lc) eR β a b) (hαβ : α ≤ β) :
    MatchedAlong (Lc := Lc) eR α a b where
  slot_eq := h.slot_eq
  fiber_bfEquiv r τ m idx x y hx hy := (h.fiber_bfEquiv r τ m idx x y hx hy).mono hαβ

/-- If `a i = .row r`, then `b i = .row (eR r)`. -/
private theorem eq_row_of_eq_row (h : MatchedAlong (Lc := Lc) eR α a b) {i : Fin n} {r : R₁}
    (hi : a i = .row r) : b i = .row (eR r) :=
  Carrier.eq_row_of_slot_eq_inl ((h.slot_eq i).trans (by simp [hi]))

/-- If `a i = .pt r τ x`, then `b i` lies in fiber `(eR r, τ)`. -/
private theorem exists_pt_of_eq_pt (h : MatchedAlong (Lc := Lc) eR α a b) {i : Fin n}
    {r : R₁} {τ : Label U} {x : C₁ r τ} (hi : a i = .pt r τ x) :
    ∃ y : C₂ (eR r) τ, b i = .pt (eR r) τ y :=
  Carrier.exists_pt_of_slot_eq_inr ((h.slot_eq i).trans (by simp [hi]))

/-- One direction of equality agreement for matched tuples at level zero. -/
private theorem eq_imp (h : MatchedAlong (Lc := Lc) eR (0 : Ordinal.{o}) a b)
    {i j : Fin n} (hij : a i = a j) : b i = b j := by
  cases hai : a i with
  | row r => rw [h.eq_row_of_eq_row hai, h.eq_row_of_eq_row (hij.symm.trans hai)]
  | pt r τ x =>
    have haj : a j = .pt r τ x := hij.symm.trans hai
    obtain ⟨y₁, hy₁⟩ := h.exists_pt_of_eq_pt hai
    obtain ⟨y₂, hy₂⟩ := h.exists_pt_of_eq_pt haj
    have hbf : BFEquiv (L := Lc) (0 : Ordinal.{o}) 2 ![x, x] ![y₁, y₂] :=
      h.fiber_bfEquiv r τ 2 ![i, j] ![x, x] ![y₁, y₂]
        (fun t => match t with | 0 => hai | 1 => haj)
        (fun t => match t with | 0 => hy₁ | 1 => hy₂)
    have hy : y₁ = y₂ := (hbf.sameAtomicType.eq_iff 0 1).mp rfl
    rw [hy₁, hy₂, hy]

/-- One direction of relation agreement for matched tuples at level zero. -/
private theorem rel_imp (h : MatchedAlong (Lc := Lc) eR (0 : Ordinal.{o}) a b)
    {k : ℕ} (s : Sym U Lc k) (f : Fin k → Fin n)
    (hs : RelMap (L := lang U Lc) s (a ∘ f)) : RelMap (L := lang U Lc) s (b ∘ f) := by
  cases s with
  | row => obtain ⟨r, hr⟩ := hs; exact ⟨eR r, h.eq_row_of_eq_row hr⟩
  | own =>
    obtain ⟨r, τ, _, h0, h1⟩ := hs
    obtain ⟨y, hy⟩ := h.exists_pt_of_eq_pt h0
    exact ⟨eR r, τ, y, hy, h.eq_row_of_eq_row h1⟩
  | lab τ =>
    obtain ⟨r, _, h0⟩ := hs
    obtain ⟨y, hy⟩ := h.exists_pt_of_eq_pt h0
    exact ⟨eR r, y, hy⟩
  | lift R =>
    obtain ⟨r, τ, x, hx, hR⟩ := hs
    let hy_ex i := h.exists_pt_of_eq_pt (hx i)
    have hbf := h.fiber_bfEquiv r τ _ f x (fun i => (hy_ex i).choose) hx
      (fun i => (hy_ex i).choose_spec)
    exact ⟨eR r, τ, fun i => (hy_ex i).choose, fun i => (hy_ex i).choose_spec,
      (hbf.sameAtomicType.rel_iff R id).mp hR⟩
  | lift0 R τ =>
    obtain ⟨r, h0, hR⟩ := hs
    have hbf := h.fiber_bfEquiv r τ 0 Fin.elim0 Fin.elim0 Fin.elim0
      (fun j => j.elim0) (fun j => j.elim0)
    have hrel := hbf.sameAtomicType.rel_iff R Fin.elim0
    rw [Subsingleton.elim (Fin.elim0 ∘ Fin.elim0) Fin.elim0,
      Subsingleton.elim (Fin.elim0 ∘ Fin.elim0) Fin.elim0] at hrel
    exact ⟨eR r, h.eq_row_of_eq_row h0, hrel.mp hR⟩

/-- Matched tuples at level zero have the same atomic type. -/
theorem sameAtomicType (h : MatchedAlong (Lc := Lc) eR (0 : Ordinal.{o}) a b) :
    SameAtomicType (L := lang U Lc) a b :=
  (sameAtomicType_iff a b).mpr
    ⟨fun _ _ => ⟨h.eq_imp, h.symm.eq_imp⟩, fun s f => ⟨h.rel_imp s f, h.symm.rel_imp s f⟩⟩

/-- Any subtuple of `snoc a p` / `snoc b q` whose indices avoid `Fin.last n` inherits fiberwise
`BFEquiv`-equivalence from `MatchedAlong`. -/
private theorem fiber_bfEquiv_snoc_of_ne_last (h : MatchedAlong (Lc := Lc) eR α a b)
    {p : Carrier R₁ C₁} {q : Carrier R₂ C₂} {r : R₁} {τ : Label U} {m : ℕ}
    {idx : Fin m → Fin (n + 1)} {x : Fin m → C₁ r τ} {y : Fin m → C₂ (eR r) τ}
    (hne : ∀ j, idx j ≠ Fin.last n)
    (hx : ∀ j, (snoc a p : Fin (n + 1) → Carrier R₁ C₁) (idx j) = Carrier.pt r τ (x j))
    (hy : ∀ j,
      (snoc b q : Fin (n + 1) → Carrier R₂ C₂) (idx j) = Carrier.pt (eR r) τ (y j)) :
    BFEquiv (L := Lc) α m x y :=
  h.fiber_bfEquiv r τ m (fun j => (idx j).castPred (hne j)) x y
    (fun j => by have := hx j; rwa [← castSucc_castPred (idx j) (hne j), snoc_castSucc] at this)
    (fun j => by have := hy j; rwa [← castSucc_castPred (idx j) (hne j), snoc_castSucc] at this)

/-- Forth extension of fiberwise matching by a row marker. -/
private theorem exists_forth_row (h : MatchedAlong (Lc := Lc) eR (α + 1) a b) (r₀ : R₁) :
    MatchedAlong (Lc := Lc) eR α (snoc a (.row r₀)) (snoc b (.row (eR r₀))) where
  slot_eq i := Fin.lastCases (by simp) (fun j => by simpa using h.slot_eq j) i
  fiber_bfEquiv _ _ _ _ _ _ hx hy :=
    (h.mono le_self_add).fiber_bfEquiv_snoc_of_ne_last (fun j hlast => by
      have h0 := hx j; rw [hlast, snoc_last] at h0; cases h0) hx hy

/-- Reindexing a subtuple landing in the extended fiber `(r₀, τ₀)` through the enumerated
existing points of `(r₀, τ₀)` together with the newly appended point. -/
private theorem fiber_bfEquiv_snoc_same_fiber {r₀ : R₁} {τ₀ : Label U}
    {x₀ : C₁ r₀ τ₀} {y₀ : C₂ (eR r₀) τ₀} {k : ℕ}
    {eS : {i : Fin n // ∃ x : C₁ r₀ τ₀, a i = .pt r₀ τ₀ x} ≃ Fin k}
    {xS : Fin k → C₁ r₀ τ₀} {yS : Fin k → C₂ (eR r₀) τ₀}
    (hxS : ∀ j, a (eS.symm j).1 = .pt r₀ τ₀ (xS j))
    (hyS : ∀ j, b (eS.symm j).1 = .pt (eR r₀) τ₀ (yS j))
    (hxy₀ : BFEquiv (L := Lc) α (k + 1) (snoc xS x₀) (snoc yS y₀))
    {m : ℕ} (idx : Fin m → Fin (n + 1)) (x : Fin m → C₁ r₀ τ₀)
    (y : Fin m → C₂ (eR r₀) τ₀)
    (hx : ∀ j, (snoc a (Carrier.pt r₀ τ₀ x₀) : Fin (n + 1) → Carrier R₁ C₁) (idx j) =
      Carrier.pt r₀ τ₀ (x j))
    (hy : ∀ j,
      (snoc b (Carrier.pt (eR r₀) τ₀ y₀) : Fin (n + 1) → Carrier R₂ C₂) (idx j) =
      Carrier.pt (eR r₀) τ₀ (y j)) :
    BFEquiv (L := Lc) α m x y := by
  have hcast {j : Fin m} (hj : idx j ≠ Fin.last n) :
      a ((idx j).castPred hj) = .pt r₀ τ₀ (x j) := by
    have := hx j; rwa [← castSucc_castPred (idx j) hj, snoc_castSucc] at this
  have hcast_b {j : Fin m} (hj : idx j ≠ Fin.last n) :
      b ((idx j).castPred hj) = .pt (eR r₀) τ₀ (y j) := by
    have := hy j; rwa [← castSucc_castPred (idx j) hj, snoc_castSucc] at this
  let g : Fin m → Fin (k + 1) := fun j =>
    if hj : idx j = Fin.last n then Fin.last k
    else (eS ⟨(idx j).castPred hj, x j, hcast hj⟩).castSucc
  have hxg : snoc xS x₀ ∘ g = x := funext fun j => by
    dsimp only [Function.comp_apply, g]
    split_ifs with hj
    · have := hx j; rw [hj, snoc_last] at this; rw [snoc_last]; exact Carrier.pt_inj_iff.mp this
    · rw [snoc_castSucc]
      have h1 := hxS (eS ⟨(idx j).castPred hj, x j, hcast hj⟩)
      rw [Equiv.symm_apply_apply] at h1
      exact Carrier.pt_inj_iff.mp (h1.symm.trans (hcast hj))
  have hyg : snoc yS y₀ ∘ g = y := funext fun j => by
    dsimp only [Function.comp_apply, g]
    split_ifs with hj
    · have := hy j; rw [hj, snoc_last] at this; rw [snoc_last]; exact Carrier.pt_inj_iff.mp this
    · rw [snoc_castSucc]
      have h1 := hyS (eS ⟨(idx j).castPred hj, x j, hcast hj⟩)
      rw [Equiv.symm_apply_apply] at h1
      exact Carrier.pt_inj_iff.mp (h1.symm.trans (hcast_b hj))
  simpa only [hxg, hyg] using hxy₀.comp g

/-- Forth extension of fiberwise matching by a fiber point. -/
private theorem exists_forth_pt (h : MatchedAlong (Lc := Lc) eR (α + 1) a b)
    (r₀ : R₁) (τ₀ : Label U) (x₀ : C₁ r₀ τ₀) :
    ∃ y₀ : C₂ (eR r₀) τ₀,
      MatchedAlong (Lc := Lc) eR α
        (snoc a (.pt r₀ τ₀ x₀)) (snoc b (.pt (eR r₀) τ₀ y₀)) := by
  classical
  -- Collect all entries of `a` lying in fiber `(r₀, τ₀)` and take one forth step there.
  let S := {i : Fin n // ∃ x : C₁ r₀ τ₀, a i = .pt r₀ τ₀ x}
  let eS : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let xS j := (eS.symm j).2.choose
  have hxS j : a (eS.symm j).1 = .pt r₀ τ₀ (xS j) := (eS.symm j).2.choose_spec
  let hyS_ex j := Carrier.exists_pt_of_slot_eq_inr (r := eR r₀) (τ := τ₀)
    ((h.slot_eq (eS.symm j).1).trans (by simp [hxS j]))
  let yS j := (hyS_ex j).choose
  have hyS j : b (eS.symm j).1 = .pt (eR r₀) τ₀ (yS j) := (hyS_ex j).choose_spec
  have hS := h.fiber_bfEquiv r₀ τ₀ _ (fun j => (eS.symm j).1) xS yS hxS hyS
  obtain ⟨y₀, hxy₀⟩ := ((BFEquiv.add_one α xS yS).mp hS).2.1 x₀
  refine ⟨y₀, fun i => Fin.lastCases (by simp) (fun j => by simpa using h.slot_eq j) i,
    fun r τ m idx x y hx hy => ?_⟩
  by_cases hrt : r = r₀ ∧ τ = τ₀
  · rcases hrt with ⟨rfl, rfl⟩
    exact fiber_bfEquiv_snoc_same_fiber hxS hyS hxy₀ idx x y hx hy
  · refine (h.mono le_self_add).fiber_bfEquiv_snoc_of_ne_last (fun j hlast => ?_) hx hy
    have hslot := congrArg Carrier.slot (hx j)
    rw [hlast, snoc_last] at hslot
    simp only [Carrier.slot_pt, Sum.inr.injEq, Prod.mk.injEq] at hslot
    exact hrt ⟨hslot.1.symm, hslot.2.symm⟩

/-- One forth step for `MatchedAlong` at a successor level. -/
private theorem exists_forth (h : MatchedAlong (Lc := Lc) eR (α + 1) a b)
    (p : Carrier R₁ C₁) :
    ∃ q : Carrier R₂ C₂, MatchedAlong (Lc := Lc) eR α (snoc a p) (snoc b q) := by
  cases p with
  | row r₀ => exact ⟨.row (eR r₀), h.exists_forth_row r₀⟩
  | pt r₀ τ₀ x₀ =>
    obtain ⟨y₀, hy₀⟩ := h.exists_forth_pt r₀ τ₀ x₀
    exact ⟨.pt (eR r₀) τ₀ y₀, hy₀⟩

/-- **Back-and-forth assembly at the same level.** If `a` and `b` are matched fiberwise at
depth `α` along a bijection of rows `eR : R₁ ≃ R₂`, then they are `BFEquiv`-equivalent at
depth `α` in the assembled language. -/
theorem bfEquiv (h : MatchedAlong (Lc := Lc) eR α a b) :
    BFEquiv (L := lang U Lc) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact BFEquiv.zero.mpr h.sameAtomicType
  | add_one α ih =>
    refine (BFEquiv.add_one α a b).mpr ⟨ih (h.mono le_self_add), fun p => ?_, fun q => ?_⟩
    · obtain ⟨q, hq⟩ := h.exists_forth p; exact ⟨q, ih hq⟩
    · obtain ⟨p, hp⟩ := h.symm.exists_forth q; exact ⟨p, ih hp.symm⟩
  | limit α hα ih =>
    exact (BFEquiv.limit hα a b).mpr fun β hβ => ih β hβ (h.mono hβ.le)

end MatchedAlong

/-- If a bijection of rows matches all fibers at depth `α` on empty tuples, then the empty tuples
of the two row assemblies are `BFEquiv`-equivalent at depth `α`. -/
theorem bfEquiv_elim0_of_rowEquiv (eR : R₁ ≃ R₂) {α : Ordinal.{o}}
    (hF : ∀ r τ, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r τ) (Fin.elim0 : Fin 0 → C₂ (eR r) τ)) :
    BFEquiv (L := lang U Lc) α 0
      (Fin.elim0 : Fin 0 → Carrier R₁ C₁) (Fin.elim0 : Fin 0 → Carrier R₂ C₂) :=
  MatchedAlong.bfEquiv (eR := eR) ⟨fun i => i.elim0, fun r τ m idx x y _ _ => by
    cases m with
    | zero => simpa only [Subsingleton.elim x Fin.elim0, Subsingleton.elim y Fin.elim0] using hF r τ
    | succ _ => exact (idx 0).elim0⟩

/-- If a bijection of rows matches all fibers at depth `α` on empty tuples, then any tuple of row
markers is `BFEquiv`-equivalent at depth `α` to its image under `eR`. -/
theorem bfEquiv_rows_of_rowEquiv (eR : R₁ ≃ R₂) {α : Ordinal.{o}}
    (hF : ∀ r τ, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r τ) (Fin.elim0 : Fin 0 → C₂ (eR r) τ))
    {n : ℕ} (rs : Fin n → R₁) :
    BFEquiv (L := lang U Lc) α n
      (fun i => (Carrier.row (rs i) : Carrier R₁ C₁))
      (fun i => (Carrier.row (eR (rs i)) : Carrier R₂ C₂)) :=
  MatchedAlong.bfEquiv (eR := eR) ⟨fun _ => by simp, fun r τ m _ x y hx _ => by
    cases m with
    | zero => simpa only [Subsingleton.elim x Fin.elim0, Subsingleton.elim y Fin.elim0] using hF r τ
    | succ _ => exact nomatch hx 0⟩

end Assembly

/-! ### Pointed fiber restriction -/

/-- Level-zero pointed restriction: tuples with the same atomic type in the assembly induce
identical atomic types on every subtuple inside a pointed fiber. -/
private theorem sameAtomicType_fiber_of_sameAtomicType [Lc.IsRelational] {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h₀ : SameAtomicType (L := lang U Lc) a b)
    {i₀ : Fin n} {r₁ : R₁} {r₂ : R₂}
    (hr₁ : a i₀ = .row r₁) (hr₂ : b i₀ = .row r₂)
    (τ : Label U) {m : ℕ} (idx : Fin m → Fin n)
    (x : Fin m → C₁ r₁ τ) (y : Fin m → C₂ r₂ τ)
    (hx : ∀ j, a (idx j) = .pt r₁ τ (x j)) (hy : ∀ j, b (idx j) = .pt r₂ τ (y j)) :
    SameAtomicType (L := Lc) x y := by
  refine (sameAtomicType_iff x y).mpr ⟨fun j₁ j₂ => ?_, fun {k} R f => ?_⟩
  · rw [← Carrier.pt_inj_iff (r := r₁) (τ := τ), ← hx j₁, ← hx j₂,
      h₀.eq_iff (idx j₁) (idx j₂), hy j₁, hy j₂, Carrier.pt_inj_iff]
  · cases k with
    | zero =>
      have hrel := h₀.rel_iff (.lift0 R τ : Sym U Lc 1) ![i₀]
      have ha : a ∘ ![i₀] = ![Carrier.row (C := C₁) r₁] := by
        ext t; simp [Subsingleton.elim t 0, hr₁]
      have hb : b ∘ ![i₀] = ![Carrier.row (C := C₂) r₂] := by
        ext t; simp [Subsingleton.elim t 0, hr₂]
      rw [ha, hb, relMap_lift0_row_iff, relMap_lift0_row_iff] at hrel
      simpa only [Subsingleton.elim (x ∘ f) Fin.elim0, Subsingleton.elim (y ∘ f) Fin.elim0]
        using hrel
    | succ l =>
      have hrel := h₀.rel_iff (.lift R : Sym U Lc (l + 1)) (idx ∘ f)
      have ha : a ∘ (idx ∘ f) = fun t => Carrier.pt r₁ τ (x (f t)) := funext fun t => hx (f t)
      have hb : b ∘ (idx ∘ f) = fun t => Carrier.pt r₂ τ (y (f t)) := funext fun t => hy (f t)
      rwa [ha, hb, relMap_lift_pt_iff, relMap_lift_pt_iff] at hrel

/-- One forth step of pointed fiber restriction: a point in fiber `(r₁, τ)` matches a point in
fiber `(r₂, τ)`. -/
private theorem exists_fiber_forth {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) (α + 1) n a b)
    {i₀ : Fin n} {r₁ : R₁} {r₂ : R₂}
    (hr₁ : a i₀ = .row r₁) (hr₂ : b i₀ = .row r₂)
    (τ : Label U) (x₀ : C₁ r₁ τ) :
    ∃ y₀ : C₂ r₂ τ,
      BFEquiv (L := lang U Lc) α (n + 1)
        (snoc a (.pt r₁ τ x₀)) (snoc b (.pt r₂ τ y₀)) := by
  obtain ⟨q, hq⟩ := ((BFEquiv.add_one α a b).mp h).2.1 (.pt r₁ τ x₀)
  have hown := hq.sameAtomicType.rel_iff (.own : Sym U Lc 2) ![Fin.last n, i₀.castSucc]
  simp only [relMap_own_iff, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, snoc_last, snoc_castSucc, hr₁, hr₂] at hown
  obtain ⟨r', τ', y₀, hqpt, hrow⟩ := hown.mp ⟨r₁, τ, x₀, rfl, rfl⟩
  obtain rfl : r₂ = r' := Carrier.row.inj hrow
  have hlab := hq.sameAtomicType.rel_iff (.lab τ : Sym U Lc 1) ![Fin.last n]
  simp only [relMap_lab_iff, Function.comp_apply, Matrix.cons_val_zero, snoc_last, hqpt] at hlab
  obtain ⟨_, _, heq⟩ := hlab.mp ⟨r₁, x₀, rfl⟩
  obtain rfl : τ' = τ := by cases heq; rfl
  exact ⟨y₀, hqpt ▸ hq⟩

/-- **Pointed fiber restriction.** If `a` and `b` are `BFEquiv`-equivalent at depth `α` and
carry `.row r₁` at position `i₀` to `.row r₂`, then any finite subtuple in fiber `(r₁, τ)` is
`BFEquiv`-equivalent at depth `α` to the corresponding subtuple in `(r₂, τ)`. -/
theorem bfEquiv_fiber_of_bfEquiv [Lc.IsRelational] {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) α n a b)
    {i₀ : Fin n} {r₁ : R₁} {r₂ : R₂}
    (hr₁ : a i₀ = .row r₁) (hr₂ : b i₀ = .row r₂)
    (τ : Label U) {m : ℕ} (idx : Fin m → Fin n)
    (x : Fin m → C₁ r₁ τ) (y : Fin m → C₂ r₂ τ)
    (hx : ∀ j, a (idx j) = .pt r₁ τ (x j)) (hy : ∀ j, b (idx j) = .pt r₂ τ (y j)) :
    BFEquiv (L := Lc) α m x y := by
  induction α using Ordinal.limitRecOn generalizing n m with
  | zero =>
    exact BFEquiv.zero.mpr (sameAtomicType_fiber_of_sameAtomicType
      (BFEquiv.zero.mp h) hr₁ hr₂ τ idx x y hx hy)
  | add_one α ih =>
    refine (BFEquiv.add_one α x y).mpr
      ⟨ih ((BFEquiv.add_one α a b).mp h).1 hr₁ hr₂ idx x y hx hy, fun x₀ => ?_, fun y₀ => ?_⟩
    · obtain ⟨y₀, hy₀⟩ := exists_fiber_forth h hr₁ hr₂ τ x₀
      exact ⟨y₀, ih hy₀ (i₀ := i₀.castSucc) (by simpa using hr₁) (by simpa using hr₂)
        (snoc (castSucc ∘ idx) (Fin.last n)) (snoc x x₀) (snoc y y₀)
        (Fin.lastCases (by simp) fun t => by simpa using hx t)
        (Fin.lastCases (by simp) fun t => by simpa using hy t)⟩
    · obtain ⟨x₀, hx₀⟩ := exists_fiber_forth h.symm hr₂ hr₁ τ y₀
      exact ⟨x₀, ih hx₀.symm (i₀ := i₀.castSucc) (by simpa using hr₁) (by simpa using hr₂)
        (snoc (castSucc ∘ idx) (Fin.last n)) (snoc x x₀) (snoc y y₀)
        (Fin.lastCases (by simp) fun t => by simpa using hx t)
        (Fin.lastCases (by simp) fun t => by simpa using hy t)⟩
  | limit α hα ih =>
    exact (BFEquiv.limit hα x y).mpr fun β hβ =>
      ih β hβ ((BFEquiv.limit hα a b).mp h β hβ) hr₁ hr₂ idx x y hx hy

/-- Equivalent single row markers have `BFEquiv`-equivalent fibers at every label. -/
theorem bfEquiv_fiber_elim0_of_bfEquiv_row [Lc.IsRelational]
    {α : Ordinal.{o}} {r₁ : R₁} {r₂ : R₂}
    (h : BFEquiv (L := lang U Lc) α 1
      (![.row r₁] : Fin 1 → Carrier R₁ C₁) (![.row r₂] : Fin 1 → Carrier R₂ C₂))
    (τ : Label U) :
    BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r₁ τ) (Fin.elim0 : Fin 0 → C₂ r₂ τ) :=
  bfEquiv_fiber_of_bfEquiv h (i₀ := 0) rfl rfl τ Fin.elim0 Fin.elim0 Fin.elim0
    (fun j => j.elim0) (fun j => j.elim0)

/-! ### Owner-row step -/

/-- **Owner-row step.** Back-and-forth equivalence of `n`-tuples at depth `β + n` extends to
equivalence at depth `β` after appending the owner row marker of every entry. -/
theorem bfEquiv_append_ownerRow {β : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) (β + n) n a b) :
    BFEquiv (L := lang U Lc) β (n + n)
      (Fin.append a fun i => .row (a i).ownerRow)
      (Fin.append b fun i => .row (b i).ownerRow) := by
  obtain ⟨y, hy⟩ := h.exists_bfEquiv_append n fun i => .row (a i).ownerRow
  have hy_eq : y = fun i => .row (b i).ownerRow := funext fun i => by
    cases hai : a i with
    | row r =>
      have heq := (hy.sameAtomicType.eq_iff (Fin.castAdd n i) (Fin.natAdd n i)).mp
        (by simp only [append_left, append_right, hai, Carrier.ownerRow_row])
      simp only [append_left, append_right] at heq
      have hrow := (hy.sameAtomicType.rel_iff (.row : Sym U Lc 1) ![Fin.castAdd n i]).mp
        ⟨r, by simp only [Function.comp_apply, Matrix.cons_val_zero, append_left, hai]⟩
      simp only [relMap_row_iff, Function.comp_apply, Matrix.cons_val_zero, append_left] at hrow
      obtain ⟨r', hbi⟩ := hrow
      rw [← heq, hbi, Carrier.ownerRow_row]
    | pt r τ x =>
      have hown := (hy.sameAtomicType.rel_iff (.own : Sym U Lc 2)
        ![Fin.castAdd n i, Fin.natAdd n i]).mp ⟨r, τ, x,
          by simp only [Function.comp_apply, Matrix.cons_val_zero, append_left, hai],
          by simp only [Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            append_right, hai, Carrier.ownerRow_pt]⟩
      simp only [relMap_own_iff, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, append_left, append_right] at hown
      obtain ⟨r', τ', x', hbi, hyi⟩ := hown
      rw [hyi, hbi, Carrier.ownerRow_pt]
  exact hy_eq ▸ hy

/-- From `BFEquiv (β + n)` between `n`-tuples `a` and `b`, every corresponding pair of owner row
markers is `BFEquiv β`-equivalent. -/
theorem bfEquiv_ownerRow_of_bfEquiv_add {β : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) (β + n) n a b) (i : Fin n) :
    BFEquiv (L := lang U Lc) β 1
      (![Carrier.row (a i).ownerRow] : Fin 1 → Carrier R₁ C₁)
      (![Carrier.row (b i).ownerRow] : Fin 1 → Carrier R₂ C₂) := by
  convert (bfEquiv_append_ownerRow h).comp (fun _ : Fin 1 => Fin.natAdd n i) using 1 <;>
    (ext t; rw [Subsingleton.elim t 0]; simp only [Function.comp_apply, append_right,
      Matrix.cons_val_zero])

end TauCeti.RowAssembly
