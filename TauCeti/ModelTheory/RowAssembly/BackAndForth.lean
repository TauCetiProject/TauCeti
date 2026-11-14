/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.Basic
public import TauCeti.ModelTheory.BackAndForth.Equivalence
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.EquivFin

/-!
# Back-and-forth transfer for row assemblies

This file relates ordinal back-and-forth equivalence `BFEquiv` on row assemblies `Carrier R C` in
the assembled language `lang U Lc` to component `Lc`-back-and-forth equivalence on the individual
fibers `C r τ`.

There are three tools:
* **Assembly (`MatchedBF.bfEquiv`)**: if `a` and `b` correspond along a row bijection `σ : R₁ ≃ R₂`
  with matching optional labels and fiberwise `Lc`-back-and-forth equivalence at depth `α` on every
  fiber (including empty tuples on unoccupied fibers), then `a` and `b` are `(lang U Lc)`-equivalent
  at depth `α`. Specializing to empty tuples gives `bfEquiv_elim0_of_rowEquiv`, and specializing to
  tuples of rows gives `bfEquiv_row_of_rowEquiv`.
* **Pointed fiber restriction (`bfEquiv_fiber_of_row_eq`)**: if `(lang U Lc)`-equivalent tuples at
  depth `β` explicitly name row elements `a i₀ = Carrier.row r₁` and `b i₀ = Carrier.row r₂`, then
  any fiber subtuples over `(r₁, τ)` and `(r₂, τ)` are `Lc`-equivalent at depth `β`.
* **Owner-row extension (`bfEquiv_append_ownerRow`)**: `n` forth steps from depth `β + n` append
  the owner rows `Carrier.row (a i).ownerRow` and force the matching entries on the right to be
  `Carrier.row (b i).ownerRow`.

## References

* Adapted from `InfinitaryLogic/ModelTheory/FiberAssembly.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized here to arbitrary ordinal depths and universe-polymorphic row assemblies.
-/

public section

universe u u₁ v₁ w₁ w₂ w₁' w₂' o

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language Fin

/-! ### Atomic-type agreement and owner-row extension -/

section OwnerRow

variable {U : Type u} {Lc : Language.{u₁, v₁}}
variable {R₁ : Type w₁} {C₁ : R₁ → Label U → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → Label U → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

/-- Tuples with the same `(lang U Lc)`-atomic type have the same optional fiber label at every
position. -/
theorem label?_eq_of_sameAtomicType {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : SameAtomicType (L := lang U Lc) a b) (i : Fin n) :
    (a i).label? = (b i).label? := by
  cases ha : (a i).label? with
  | none =>
    have hb := (h.rel_iff Sym.row (fun _ => i)).mp (by simp [ha])
    simpa using hb.symm
  | some τ =>
    have hb := (h.rel_iff (Sym.lab τ) (fun _ => i)).mp (by simp [ha])
    simpa using hb.symm

/-- Appending the owner rows of an `n`-tuple consumes `n` back-and-forth levels and forces the
matching entries on the right to be the owner rows of `b`. The component language `Lc` need not be
relational. -/
theorem bfEquiv_append_ownerRow {β : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) (β + n) n a b) :
    BFEquiv (L := lang U Lc) β (n + n)
      (Fin.append a (fun i => .row (a i).ownerRow))
      (Fin.append b (fun i => .row (b i).ownerRow)) := by
  obtain ⟨y, hy⟩ := BFEquiv.exists_bfEquiv_append n h (fun i => .row (a i).ownerRow)
  have hsat := hy.sameAtomicType
  have hy_eq : y = fun i => .row (b i).ownerRow := by
    funext i
    have hrow : (y i).label? = none := by
      have hr := (hsat.rel_iff Sym.row (fun _ => natAdd n i)).mp
        (by simp only [relMap_row_iff, Function.comp_apply, append_right, Carrier.label?_row])
      simpa only [relMap_row_iff, Function.comp_apply, append_right] using hr
    have hyi : y i = .row (y i).ownerRow := Carrier.label?_eq_none_iff.mp hrow
    cases hai : a i with
    | row r =>
      have heq : Fin.append a (fun j => .row (a j).ownerRow) (castAdd n i) =
          Fin.append a (fun j => .row (a j).ownerRow) (natAdd n i) := by
        simp only [append_left, append_right, hai, Carrier.ownerRow_row]
      have hbeq := (hsat.eq_iff (castAdd n i) (natAdd n i)).mp heq
      simp only [append_left, append_right] at hbeq
      rw [hbeq, hyi, Carrier.ownerRow_row]
    | pt r τ x =>
      let f : Fin 2 → Fin (n + n) := Fin.cons (castAdd n i) (fun _ => natAdd n i)
      have hown : Structure.RelMap (L := lang U Lc) Sym.own
          (Fin.append a (fun j => .row (a j).ownerRow) ∘ f) := by
        simp only [relMap_own_iff, Function.comp_apply, f, cons_zero, cons_one,
          append_left, append_right, hai]
        simp
      have hown' := (hsat.rel_iff Sym.own f).mp hown
      simp only [relMap_own_iff, Function.comp_apply, f, cons_zero, cons_one,
        append_left, append_right] at hown'
      rw [hyi, hown'.2.2]
  rwa [hy_eq] at hy

end OwnerRow

/-! ### Assembling back-and-forth equivalence from fiberwise equivalence -/

section Assembly

variable {U : Type u} {Lc : Language.{u₁, v₁}} [Lc.IsRelational]
variable {R₁ : Type w₁} {C₁ : R₁ → Label U → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → Label U → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

/-- Fiberwise back-and-forth matching of `n`-tuples `a` in `Carrier R₁ C₁` and `b` in
`Carrier R₂ C₂` at ordinal depth `α` along a row bijection `σ : R₁ ≃ R₂`:
* `(b i).ownerRow = σ (a i).ownerRow` and `(b i).label? = (a i).label?` at every position `i`;
* for every fiber `(r, τ)` and any tuple of positions `idx : Fin m → Fin n` whose entries in `a`
  and `b` are presented as fiber points `xs` and `ys`, `BFEquiv α m xs ys` holds in `Lc`.

Taking `m = 0` (`Fin.elim0`) includes empty-tuple `Lc`-equivalence on every fiber `(r, τ)`. -/
structure MatchedBF (σ : R₁ ≃ R₂) (α : Ordinal.{o}) {n : ℕ}
    (a : Fin n → Carrier R₁ C₁) (b : Fin n → Carrier R₂ C₂) : Prop where
  /-- Owner rows correspond under `σ`. -/
  ownerRow_eq : ∀ i, (b i).ownerRow = σ (a i).ownerRow
  /-- Optional fiber labels agree pointwise. -/
  label?_eq : ∀ i, (b i).label? = (a i).label?
  /-- Subtuples landing in a common fiber are `Lc`-equivalent at depth `α`. -/
  fiber_bfEquiv : ∀ (r : R₁) (τ : Label U) {m : ℕ} (idx : Fin m → Fin n)
      (xs : Fin m → C₁ r τ) (ys : Fin m → C₂ (σ r) τ),
      (∀ k, a (idx k) = .pt r τ (xs k)) →
      (∀ k, b (idx k) = .pt (σ r) τ (ys k)) →
      BFEquiv (L := Lc) α m xs ys

namespace MatchedBF

/-- Monotonicity of `MatchedBF` in the ordinal depth. -/
theorem mono {σ : R₁ ≃ R₂} {α β : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ β a b) (hαβ : α ≤ β) :
    MatchedBF (Lc := Lc) σ α a b :=
  ⟨h.ownerRow_eq, h.label?_eq, fun r τ {_} idx xs ys hxs hys =>
    (h.fiber_bfEquiv r τ idx xs ys hxs hys).mono hαβ⟩

/-- Symmetry of `MatchedBF` along `σ.symm`. -/
theorem symm {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) :
    MatchedBF (Lc := Lc) σ.symm α b a where
  ownerRow_eq i := σ.eq_symm_apply.mpr (h.ownerRow_eq i).symm
  label?_eq i := (h.label?_eq i).symm
  fiber_bfEquiv r' τ {m} idx := by
    obtain ⟨r, rfl⟩ := σ.surjective r'
    rw [σ.symm_apply_apply r]
    intro ys xs hys hxs
    exact (h.fiber_bfEquiv r τ idx xs ys hxs hys).symm

private theorem eq_row_of_row {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) {i : Fin n} {r : R₁} (hai : a i = .row r) :
    b i = .row (σ r) := by
  have hl : (b i).label? = none := by rw [h.label?_eq i, hai, Carrier.label?_row]
  have hb := Carrier.label?_eq_none_iff.mp hl
  rw [h.ownerRow_eq i, hai, Carrier.ownerRow_row] at hb
  exact hb

private theorem exists_pt_of_pt {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) {i : Fin n} {r : R₁} {τ : Label U} (x : C₁ r τ)
    (hai : a i = .pt r τ x) :
    ∃ y : C₂ (σ r) τ, b i = .pt (σ r) τ y := by
  have ho : (b i).ownerRow = σ r := by rw [h.ownerRow_eq i, hai, Carrier.ownerRow_pt]
  have hl : (b i).label? = some τ := by rw [h.label?_eq i, hai, Carrier.label?_pt]
  exact Carrier.ownerRow_eq_and_label?_eq_some_iff.mp ⟨ho, hl⟩

private theorem eq_imp {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) {i j : Fin n} (haij : a i = a j) :
    b i = b j := by
  cases hai : a i with
  | row r =>
    exact (h.eq_row_of_row hai).trans (h.eq_row_of_row (haij.symm.trans hai)).symm
  | pt r τ x =>
    have haj : a j = .pt r τ x := haij.symm.trans hai
    obtain ⟨yi, hbi⟩ := h.exists_pt_of_pt x hai
    obtain ⟨yj, hbj⟩ := h.exists_pt_of_pt x haj
    have hf := h.fiber_bfEquiv r τ (m := 2) (Fin.cons i (fun _ => j))
      (Fin.cons x (fun _ => x)) (Fin.cons yi (fun _ => yj))
      (Fin.cases (by simpa using hai) fun _ => by simpa using haj)
      (Fin.cases (by simpa using hbi) fun _ => by simpa using hbj)
    have hyij : yi = yj := (hf.sameAtomicType.eq_iff 0 1).mp rfl
    rw [hbi, hbj, hyij]

private theorem rel_imp {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n k : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) (s : Sym U Lc k) (f : Fin k → Fin n)
    (hs : Structure.RelMap (L := lang U Lc) s (a ∘ f)) :
    Structure.RelMap (L := lang U Lc) s (b ∘ f) := by
  cases s with
  | row =>
    simp only [relMap_row_iff, Function.comp_apply] at hs ⊢
    rwa [h.label?_eq]
  | own =>
    simp only [relMap_own_iff, Function.comp_apply] at hs ⊢
    exact ⟨by rw [h.label?_eq]; exact hs.1, by rw [h.label?_eq]; exact hs.2.1,
      by rw [h.ownerRow_eq, h.ownerRow_eq, hs.2.2]⟩
  | lab τ =>
    simp only [relMap_lab_iff, Function.comp_apply] at hs ⊢
    rwa [h.label?_eq]
  | lift rel =>
    simp only [relMap_lift_iff, Function.comp_apply] at hs ⊢
    obtain ⟨r, τ, xs, hxs, hR⟩ := hs
    choose ys hys using fun j => h.exists_pt_of_pt (xs j) (hxs j)
    have hf := h.fiber_bfEquiv r τ f xs ys hxs hys
    exact ⟨σ r, τ, ys, hys, (hf.sameAtomicType.rel_iff rel id).mp hR⟩
  | lift0 rel τ =>
    simp only [relMap_lift0_iff, Function.comp_apply] at hs ⊢
    obtain ⟨r, hr, hR⟩ := hs
    have hf := h.fiber_bfEquiv r τ Fin.elim0 Fin.elim0 Fin.elim0
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    refine ⟨σ r, h.eq_row_of_row hr, ?_⟩
    have hR' := (hf.sameAtomicType.rel_iff rel Fin.elim0).mp
      (by rwa [Subsingleton.elim (Fin.elim0 ∘ Fin.elim0) Fin.elim0])
    rwa [Subsingleton.elim (Fin.elim0 ∘ Fin.elim0) Fin.elim0] at hR'

/-- Tuples related by `MatchedBF` at any depth have the same `(lang U Lc)`-atomic type. -/
theorem sameAtomicType {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) :
    SameAtomicType (L := lang U Lc) a b :=
  (sameAtomicType_iff a b).mpr
    ⟨fun _ _ => ⟨h.eq_imp, h.symm.eq_imp⟩, fun s f => ⟨h.rel_imp s f, h.symm.rel_imp s f⟩⟩

private theorem forth_row {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ (α + 1) a b) (r₀ : R₁) :
    MatchedBF (Lc := Lc) σ α (snoc a (.row r₀)) (snoc b (.row (σ r₀))) where
  ownerRow_eq := lastCases (by simp) fun i => by simp [h.ownerRow_eq]
  label?_eq := lastCases (by simp) fun i => by simp [h.label?_eq]
  fiber_bfEquiv r τ {m} idx xs ys hxs hys := by
    have hcast : ∀ k : Fin m, ∃ j : Fin n, idx k = castSucc j := by
      intro k
      generalize hk : idx k = ik
      cases ik using Fin.lastCases with
      | last =>
        have hbad := hxs k
        rw [hk, snoc_last] at hbad
        cases hbad
      | cast j => exact ⟨j, rfl⟩
    choose idx' hidx' using hcast
    exact (h.fiber_bfEquiv r τ idx' xs ys
      (fun k => by simpa [hidx' k] using hxs k)
      (fun k => by simpa [hidx' k] using hys k)).mono le_self_add

private theorem fiber_bfEquiv_snoc_pt_of_ne {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n m : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ (α + 1) a b)
    {r₀ r : R₁} {τ₀ τ : Label U} (hrt : ¬ (r = r₀ ∧ τ = τ₀))
    (x₀ : C₁ r₀ τ₀) (y₀ : C₂ (σ r₀) τ₀)
    (idx : Fin m → Fin (n + 1)) (xs : Fin m → C₁ r τ) (ys : Fin m → C₂ (σ r) τ)
    (hxs : ∀ k, snoc (α := fun _ => Carrier R₁ C₁) a (.pt r₀ τ₀ x₀) (idx k) = .pt r τ (xs k))
    (hys : ∀ k, snoc (α := fun _ => Carrier R₂ C₂) b (.pt (σ r₀) τ₀ y₀) (idx k) =
      .pt (σ r) τ (ys k)) :
    BFEquiv (L := Lc) α m xs ys := by
  have hcast : ∀ k : Fin m, ∃ j : Fin n, idx k = castSucc j := fun k => by
    generalize hk : idx k = ik
    cases ik using Fin.lastCases with
    | last =>
      have hbad : (.pt r₀ τ₀ x₀ : Carrier R₁ C₁) = .pt r τ (xs k) := by simpa [hk] using hxs k
      injection hbad with hr hτ _
      exact False.elim (hrt ⟨hr.symm, hτ.symm⟩)
    | cast j => exact ⟨j, rfl⟩
  choose idx' hidx' using hcast
  exact (h.fiber_bfEquiv r τ idx' xs ys
    (fun k => by simpa [hidx' k] using hxs k)
    (fun k => by simpa [hidx' k] using hys k)).mono le_self_add

private theorem forth_pt {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ (α + 1) a b) (r₀ : R₁) (τ₀ : Label U) (x₀ : C₁ r₀ τ₀) :
    ∃ y₀ : C₂ (σ r₀) τ₀,
      MatchedBF (Lc := Lc) σ α (snoc a (.pt r₀ τ₀ x₀)) (snoc b (.pt (σ r₀) τ₀ y₀)) := by
  classical
  let P : Fin n → Prop := fun i => (a i).ownerRow = r₀ ∧ (a i).label? = some τ₀
  let m₀ := Fintype.card {i : Fin n // P i}
  let e₀ : Fin m₀ ≃ {i : Fin n // P i} := (Fintype.equivFin {i : Fin n // P i}).symm
  let idx₀ : Fin m₀ → Fin n := fun q => (e₀ q).1
  choose xs₀ hxs₀ using fun q => Carrier.ownerRow_eq_and_label?_eq_some_iff.mp (e₀ q).2
  choose ys₀ hys₀ using fun q => h.exists_pt_of_pt (xs₀ q) (hxs₀ q)
  obtain ⟨y₀, hy₀⟩ := ((BFEquiv.add_one α xs₀ ys₀).mp
    (h.fiber_bfEquiv r₀ τ₀ idx₀ xs₀ ys₀ hxs₀ hys₀)).2.1 x₀
  refine ⟨y₀, lastCases (by simp) fun i => by simp [h.ownerRow_eq],
    lastCases (by simp) fun i => by simp [h.label?_eq], fun r τ {m} idx xs ys hxs hys => ?_⟩
  by_cases hrt : r = r₀ ∧ τ = τ₀
  · rcases hrt with ⟨rfl, rfl⟩
    have hg : ∀ k : Fin m, ∃ t : Fin (m₀ + 1),
        xs k = snoc (α := fun _ => C₁ r τ) xs₀ x₀ t ∧
        ys k = snoc (α := fun _ => C₂ (σ r) τ) ys₀ y₀ t := fun k => by
      generalize hk : idx k = ik
      cases ik using Fin.lastCases with
      | last =>
        refine ⟨last m₀, ?_, ?_⟩
        · rw [snoc_last]
          exact (Carrier.pt_injective r τ (by simpa [hk] using hxs k)).symm
        · rw [snoc_last]
          exact (Carrier.pt_injective (σ r) τ (by simpa [hk] using hys k)).symm
      | cast j =>
        have haj : a j = .pt r τ (xs k) := by simpa [hk] using hxs k
        have hbj : b j = .pt (σ r) τ (ys k) := by simpa [hk] using hys k
        let q : Fin m₀ := e₀.symm ⟨j, by simp [P, haj]⟩
        have hqj : idx₀ q = j := congrArg Subtype.val (e₀.apply_symm_apply _)
        exact ⟨castSucc q,
          (snoc_castSucc _ _ _).symm ▸ Carrier.pt_injective r τ (haj.symm.trans (hqj ▸ hxs₀ q)),
          (snoc_castSucc _ _ _).symm ▸
            Carrier.pt_injective (σ r) τ (hbj.symm.trans (hqj ▸ hys₀ q))⟩
    choose g hgx hgy using hg
    rw [funext hgx, funext hgy]
    exact hy₀.comp g
  · exact fiber_bfEquiv_snoc_pt_of_ne h hrt x₀ y₀ idx xs ys hxs hys

/-- Forth step for `MatchedBF` from depth `α + 1` to depth `α`. -/
theorem forth {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ (α + 1) a b) (u : Carrier R₁ C₁) :
    ∃ v : Carrier R₂ C₂, MatchedBF (Lc := Lc) σ α (snoc a u) (snoc b v) := by
  cases u with
  | row r₀ => exact ⟨.row (σ r₀), h.forth_row r₀⟩
  | pt r₀ τ₀ x₀ =>
    obtain ⟨y₀, hy₀⟩ := h.forth_pt r₀ τ₀ x₀
    exact ⟨.pt (σ r₀) τ₀ y₀, hy₀⟩

/-- Fiberwise back-and-forth matching along `σ` at ordinal depth `α` implies `(lang U Lc)`
back-and-forth equivalence at depth `α`. -/
theorem bfEquiv {σ : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : MatchedBF (Lc := Lc) σ α a b) :
    BFEquiv (L := lang U Lc) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact BFEquiv.zero.mpr h.sameAtomicType
  | add_one α ih =>
    refine (BFEquiv.add_one α a b).mpr ⟨ih (h.mono le_self_add), ?_, ?_⟩
    · intro u
      obtain ⟨v, hv⟩ := h.forth u
      exact ⟨v, ih hv⟩
    · intro v
      obtain ⟨u, hu⟩ := h.symm.forth v
      exact ⟨u, ih hu.symm⟩
  | limit α hα ih =>
    exact (BFEquiv.limit hα a b).mpr fun β hβ => ih β hβ (h.mono hβ.le)

end MatchedBF

/-- If a row bijection `σ : R₁ ≃ R₂` matches every fiber `(r, τ)` with `(σ r, τ)` at empty-tuple
`Lc`-depth `α`, then any tuple of rows `rs : Fin n → R₁` is `(lang U Lc)`-equivalent at depth `α`
to `σ ∘ rs`. -/
theorem bfEquiv_row_of_rowEquiv (σ : R₁ ≃ R₂) (α : Ordinal.{o}) {n : ℕ} (rs : Fin n → R₁)
    (hf : ∀ r τ, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r τ) (Fin.elim0 : Fin 0 → C₂ (σ r) τ)) :
    BFEquiv (L := lang U Lc) α n
      (fun i => Carrier.row (rs i) : Fin n → Carrier R₁ C₁)
      (fun i => Carrier.row (σ (rs i)) : Fin n → Carrier R₂ C₂) := by
  refine (MatchedBF.mk (σ := σ) (fun _ => by simp) (fun _ => by simp) ?_).bfEquiv
  intro r τ m idx xs ys hxs _
  cases m with
  | zero =>
    rw [Subsingleton.elim xs Fin.elim0, Subsingleton.elim ys Fin.elim0]
    exact hf r τ
  | succ l =>
    have hbad := hxs 0
    cases hbad

/-- If a row bijection `σ : R₁ ≃ R₂` matches every fiber `(r, τ)` with `(σ r, τ)` at empty-tuple
`Lc`-depth `α`, then the assembled structures are `(lang U Lc)`-equivalent on empty tuples at
depth `α`. -/
theorem bfEquiv_elim0_of_rowEquiv (σ : R₁ ≃ R₂) (α : Ordinal.{o})
    (hf : ∀ r τ, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r τ) (Fin.elim0 : Fin 0 → C₂ (σ r) τ)) :
    BFEquiv (L := lang U Lc) α 0
      (Fin.elim0 : Fin 0 → Carrier R₁ C₁) (Fin.elim0 : Fin 0 → Carrier R₂ C₂) := by
  convert bfEquiv_row_of_rowEquiv σ α Fin.elim0 hf

end Assembly

/-! ### Restricting back-and-forth equivalence to pointed fibers -/

section Restriction

variable {U : Type u} {Lc : Language.{u₁, v₁}}
variable {R₁ : Type w₁} {C₁ : R₁ → Label U → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → Label U → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

private theorem forth_fiber_of_row_eq {β : Ordinal.{o}} {N m : ℕ}
    {a : Fin N → Carrier R₁ C₁} {b : Fin N → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) (β + 1) N a b)
    {i₀ : Fin N} {r₁ : R₁} {r₂ : R₂} (ha₀ : a i₀ = .row r₁) (hb₀ : b i₀ = .row r₂)
    (τ : Label U) (idx : Fin m → Fin N) (xs : Fin m → C₁ r₁ τ) (ys : Fin m → C₂ r₂ τ)
    (hxs : ∀ k, a (idx k) = .pt r₁ τ (xs k)) (hys : ∀ k, b (idx k) = .pt r₂ τ (ys k))
    (x : C₁ r₁ τ) :
    ∃ y : C₂ r₂ τ,
      BFEquiv (L := lang U Lc) β (N + 1)
        (snoc a (Carrier.pt r₁ τ x)) (snoc b (Carrier.pt r₂ τ y)) ∧
      (∀ k : Fin (m + 1), snoc (α := fun _ => Carrier R₁ C₁) a (Carrier.pt r₁ τ x)
          (snoc (α := fun _ => Fin (N + 1)) (castSucc ∘ idx) (last N) k) =
        Carrier.pt r₁ τ (snoc (α := fun _ => C₁ r₁ τ) xs x k)) ∧
      (∀ k : Fin (m + 1), snoc (α := fun _ => Carrier R₂ C₂) b (Carrier.pt r₂ τ y)
          (snoc (α := fun _ => Fin (N + 1)) (castSucc ∘ idx) (last N) k) =
        Carrier.pt r₂ τ (snoc (α := fun _ => C₂ r₂ τ) ys y k)) := by
  obtain ⟨v, hv⟩ := ((BFEquiv.add_one β a b).mp h).2.1 (.pt r₁ τ x)
  have hsat := hv.sameAtomicType
  have hv_lab : v.label? = some τ := by
    have hl := label?_eq_of_sameAtomicType hsat (last N)
    simpa using hl.symm
  have hv_row : v.ownerRow = r₂ := by
    let f : Fin 2 → Fin (N + 1) := Fin.cons (last N) (fun _ => castSucc i₀)
    have hown : Structure.RelMap (L := lang U Lc) Sym.own (snoc a (.pt r₁ τ x) ∘ f) := by
      simp [f, ha₀]
    have hown' := (hsat.rel_iff Sym.own f).mp hown
    simp only [relMap_own_iff, Function.comp_apply, f, cons_zero, cons_one,
      snoc_last, snoc_castSucc, hb₀, Carrier.ownerRow_row] at hown'
    exact hown'.2.2
  obtain ⟨y, rfl⟩ := Carrier.ownerRow_eq_and_label?_eq_some_iff.mp ⟨hv_row, hv_lab⟩
  exact ⟨y, hv,
    lastCases (by simp) fun k => by simp [hxs k],
    lastCases (by simp) fun k => by simp [hys k]⟩

variable [Lc.IsRelational]

/-- **Pointed fiber restriction**: if `(lang U Lc)`-equivalent tuples `a` and `b` at depth `β`
contain row elements `a i₀ = Carrier.row r₁` and `b i₀ = Carrier.row r₂`, then any subtuples `xs`
and `ys` of fiber points over `(r₁, τ)` and `(r₂, τ)` at matching positions `idx` are
`Lc`-equivalent at depth `β`. -/
theorem bfEquiv_fiber_of_row_eq {β : Ordinal.{o}} {N m : ℕ}
    {a : Fin N → Carrier R₁ C₁} {b : Fin N → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) β N a b)
    {i₀ : Fin N} {r₁ : R₁} {r₂ : R₂} (ha₀ : a i₀ = .row r₁) (hb₀ : b i₀ = .row r₂)
    (τ : Label U) (idx : Fin m → Fin N) (xs : Fin m → C₁ r₁ τ) (ys : Fin m → C₂ r₂ τ)
    (hxs : ∀ k, a (idx k) = .pt r₁ τ (xs k)) (hys : ∀ k, b (idx k) = .pt r₂ τ (ys k)) :
    BFEquiv (L := Lc) β m xs ys := by
  induction β using Ordinal.limitRecOn generalizing N m with
  | zero =>
    have hsat := BFEquiv.zero.mp h
    refine BFEquiv.zero.mpr ((sameAtomicType_iff xs ys).mpr ⟨fun j k => ?_, fun {d} rel f => ?_⟩)
    · rw [← (Carrier.pt_injective r₁ τ).eq_iff, ← hxs j, ← hxs k,
        hsat.eq_iff (idx j) (idx k), hys j, hys k, (Carrier.pt_injective r₂ τ).eq_iff]
    · cases d with
      | zero =>
        have h0 := hsat.rel_iff (Sym.lift0 rel τ) (fun _ => i₀)
        simp only [Function.comp_def, ha₀, hb₀, relMap_lift0_row_iff] at h0
        rwa [Subsingleton.elim (xs ∘ f) Fin.elim0, Subsingleton.elim (ys ∘ f) Fin.elim0]
      | succ l =>
        have hl := hsat.rel_iff (Sym.lift rel) (idx ∘ f)
        have hax : a ∘ (idx ∘ f) = fun j => Carrier.pt r₁ τ ((xs ∘ f) j) :=
          funext fun j => hxs (f j)
        have hby : b ∘ (idx ∘ f) = fun j => Carrier.pt r₂ τ ((ys ∘ f) j) :=
          funext fun j => hys (f j)
        rw [hax, hby, relMap_lift_pt_iff, relMap_lift_pt_iff] at hl
        exact hl
  | add_one β ih =>
    refine (BFEquiv.add_one β xs ys).mpr
      ⟨ih (h.mono le_self_add) ha₀ hb₀ idx xs ys hxs hys, ?_, ?_⟩
    · intro x
      obtain ⟨y, hv, hx', hy'⟩ := forth_fiber_of_row_eq h ha₀ hb₀ τ idx xs ys hxs hys x
      exact ⟨y, ih hv (i₀ := castSucc i₀) (by simp [ha₀]) (by simp [hb₀]) _ _ _ hx' hy'⟩
    · intro y
      obtain ⟨x, hu, hy', hx'⟩ := forth_fiber_of_row_eq h.symm hb₀ ha₀ τ idx ys xs hys hxs y
      exact ⟨x, ih hu.symm (i₀ := castSucc i₀) (by simp [ha₀]) (by simp [hb₀]) _ _ _ hx' hy'⟩
  | limit β hβ ih =>
    exact (BFEquiv.limit hβ xs ys).mpr fun γ hγ =>
      ih γ hγ ((BFEquiv.limit hβ a b).mp h γ hγ) ha₀ hb₀ idx xs ys hxs hys

/-- Special case of `bfEquiv_fiber_of_row_eq` for empty fiber tuples: when `a i₀ = Carrier.row r₁`
and `b i₀ = Carrier.row r₂` correspond at depth `β`, every fiber `(r₁, τ)` is `Lc`-equivalent on
empty tuples at depth `β` to `(r₂, τ)`. -/
theorem bfEquiv_fiber_elim0_of_row_eq {β : Ordinal.{o}} {N : ℕ}
    {a : Fin N → Carrier R₁ C₁} {b : Fin N → Carrier R₂ C₂}
    (h : BFEquiv (L := lang U Lc) β N a b)
    {i₀ : Fin N} {r₁ : R₁} {r₂ : R₂} (ha₀ : a i₀ = .row r₁) (hb₀ : b i₀ = .row r₂)
    (τ : Label U) :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → C₁ r₁ τ) (Fin.elim0 : Fin 0 → C₂ r₂ τ) :=
  bfEquiv_fiber_of_row_eq h ha₀ hb₀ τ Fin.elim0 Fin.elim0 Fin.elim0
    (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)

end Restriction

end TauCeti.RowAssembly
