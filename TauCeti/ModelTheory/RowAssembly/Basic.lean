/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
import Mathlib.Basic.Countable.Basic

/-!
# Row assemblies of labelled fibers

Given a fiber label type `ι` and a component language `Lc`, a **row assembly** builds a relational
structure `Carrier R C` over a type `R` of rows and a family `C r τ` of component `Lc`-structures
indexed by rows `r : R` and labels `τ : ι`.

The assembled relational language `lang ι Lc` carries:
* a unary predicate `Sym.row` picking out the rows;
* a binary predicate `Sym.own` relating each fiber point `Carrier.pt r τ x` to its owner row
  `Carrier.row r`;
* a unary predicate `Sym.lab τ` picking out the points of label `τ`;
* for each `(l + 1)`-ary relation symbol `rel` of `Lc`, a lifted `(l + 1)`-ary symbol
  `Sym.lift rel` holding on tuples of fiber points that share one row and one label and satisfy
  `rel` in that fiber;
* for each nullary relation symbol `rel` of `Lc` and label `τ`, a unary symbol `Sym.lift0 rel τ`
  read at `Carrier.row r` as the truth of `rel` in `C r τ`.

Because rows, ownership, and labels are explicit in the signature, every isomorphism between two
row assemblies restricts to a bijection of rows (`FirstOrder.Language.Equiv.rowEquiv`) together with
fiberwise bijections (`FirstOrder.Language.Equiv.fiberToEquiv`), which upgrade to `Lc`-isomorphisms
(`FirstOrder.Language.Equiv.fiberEquiv`) when `Lc` is relational; conversely, any row bijection and
family of fiber `Lc`-isomorphisms assemble into an isomorphism of row assemblies (`equivOfFibers`).

## Main definitions

* `TauCeti.RowAssembly.Sym ι Lc` and `TauCeti.RowAssembly.lang ι Lc`: the relation symbols and
  relational language of row assemblies.
* `TauCeti.RowAssembly.Carrier R C`: the disjoint union of rows `r : R` and fiber points
  `x : C r τ`, equipped with its `(lang ι Lc)`-structure.
* `TauCeti.RowAssembly.equivOfFibers`: assemble an isomorphism from a row bijection and fiber
  isomorphisms.
* `FirstOrder.Language.Equiv.rowEquiv`, `FirstOrder.Language.Equiv.fiberToEquiv`, and
  `FirstOrder.Language.Equiv.fiberEquiv`: restrict an isomorphism of row assemblies to its induced
  row bijection and fiber bijections / `Lc`-isomorphisms.

## References

* The row-assembly signature, carrier, and isomorphism assembly/restriction are adapted from
  `InfinitaryLogic/ModelTheory/FiberAssembly.lean` and
  `InfinitaryLogic/ModelTheory/FiberIsoAssembly.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized here to an arbitrary universe-polymorphic fiber label type, component
  language, row type, and fiber carriers.
-/

public section

universe u u₁ v₁ w₁ w₂ w₁' w₂'

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language

/-! ### The assembled relational language -/

/-- The relation symbols of the assembled language over fiber label type `ι` and component language
`Lc`: rows, ownership, fiber labels, lifted positive-arity component relations, and lifted nullary
component relations read at the owner row. -/
inductive Sym (ι : Type u) (Lc : Language.{u₁, v₁}) : ℕ → Type (max u v₁)
  /-- Unary predicate holding of the row elements `Carrier.row r`. -/
  | row : Sym ι Lc 1
  /-- Binary ownership relation holding of `(Carrier.pt r τ x, Carrier.row r)`. -/
  | own : Sym ι Lc 2
  /-- Unary predicate holding of the fiber elements `Carrier.pt r τ x` with label `τ`. -/
  | lab (τ : ι) : Sym ι Lc 1
  /-- Positive-arity relation symbol of `Lc`, holding on tuples within a single fiber `(r, τ)`. -/
  | lift {l : ℕ} (rel : Lc.Relations (l + 1)) : Sym ι Lc (l + 1)
  /-- Nullary relation symbol of `Lc` at label `τ`, holding at `Carrier.row r` when `rel` holds in
  `C r τ`. -/
  | lift0 (rel : Lc.Relations 0) (τ : ι) : Sym ι Lc 1

/-- The relational language of row assemblies over fiber label type `ι` and component language `Lc`.
The definition is reducible so that relation symbols of `lang ι Lc` are directly `Sym ι Lc`. -/
abbrev lang (ι : Type u) (Lc : Language.{u₁, v₁}) : Language.{0, max u v₁} where
  Functions _ := PEmpty
  Relations := Sym ι Lc

instance isRelational_lang (ι : Type u) (Lc : Language.{u₁, v₁}) : (lang ι Lc).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty PEmpty)

/-- When the label type `ι` and the relation symbols of `Lc` at arities `0` and `n` are countable,
arity `n` of `lang ι Lc` has countably many relation symbols. -/
instance countable_relations_lang (ι : Type u) (Lc : Language.{u₁, v₁}) (n : ℕ) [Countable ι]
    [Countable (Lc.Relations 0)] [Countable (Lc.Relations n)] :
    Countable ((lang ι Lc).Relations n) := by
  let enc : Option (Bool ⊕ ι ⊕ (Lc.Relations 0 × ι)) ⊕ Lc.Relations n →
      Option (Sym ι Lc n)
    | .inl none => if h : n = 2 then some (h ▸ .own) else none
    | .inl (some (.inl false)) => if h : n = 1 then some (h ▸ .row) else none
    | .inl (some (.inl true)) => none
    | .inl (some (.inr (.inl τ))) => if h : n = 1 then some (h ▸ .lab τ) else none
    | .inl (some (.inr (.inr (rel, τ)))) => if h : n = 1 then some (h ▸ .lift0 rel τ) else none
    | .inr rel =>
      match n, rel with
      | 0, _ => none
      | _ + 1, rel => some (.lift rel)
  have hsurj : ∀ s : Sym ι Lc n, ∃ x, enc x = some s := by
    intro s
    cases s with
    | row => exact ⟨.inl (some (.inl false)), by simp [enc]⟩
    | own => exact ⟨.inl none, by simp [enc]⟩
    | lab τ => exact ⟨.inl (some (.inr (.inl τ))), by simp [enc]⟩
    | lift rel => exact ⟨.inr rel, rfl⟩
    | lift0 rel τ => exact ⟨.inl (some (.inr (.inr (rel, τ)))), by simp [enc]⟩
  choose g hg using hsurj
  exact Function.Injective.countable (f := g) fun a b hab => Option.some_injective _
    ((hg a).symm.trans ((congrArg enc hab).trans (hg b)))

/-! ### The assembled carrier and its projections -/

/-- The carrier of a row assembly: one element `row r` for each `r : R`, and one element
`pt r τ x` for each point `x` of the fiber `C r τ`. -/
inductive Carrier {ι : Type u} (R : Type w₁) (C : R → ι → Type w₂) : Type (max u w₁ w₂)
  /-- A row element. -/
  | row (r : R)
  /-- A point of the fiber over row `r` with label `τ`. -/
  | pt (r : R) (τ : ι) (x : C r τ)

namespace Carrier

variable {ι : Type u} {R : Type w₁} {C : R → ι → Type w₂}

/-- Injectivity of `pt` in the fiber point when row and label are fixed. -/
theorem pt_injective (r : R) (τ : ι) : Function.Injective (pt r τ : C r τ → Carrier R C) := by
  intro _ _ h
  cases h
  rfl

/-- The owner row of an element: `r` on both `row r` and `pt r τ x`. -/
def ownerRow : Carrier R C → R
  | row r => r
  | pt r _ _ => r

@[simp]
theorem ownerRow_row (r : R) : ownerRow (row r : Carrier R C) = r := (rfl)

@[simp]
theorem ownerRow_pt (r : R) (τ : ι) (x : C r τ) : ownerRow (pt r τ x) = r := (rfl)

/-- The optional fiber label of an element: `none` on rows and `some τ` on points of fiber `τ`. -/
def label? : Carrier R C → Option ι
  | row _ => none
  | pt _ τ _ => some τ

@[simp]
theorem label?_row (r : R) : label? (row r : Carrier R C) = none := (rfl)

@[simp]
theorem label?_pt (r : R) (τ : ι) (x : C r τ) : label? (pt r τ x) = some τ := (rfl)

/-- An element has `label? u = none` precisely when it is the row of its `ownerRow`. -/
theorem label?_eq_none_iff {u : Carrier R C} : label? u = none ↔ u = row (ownerRow u) := by
  cases u <;> simp

/-- An element has `ownerRow u = r` and `label? u = some τ` precisely when it lies in `C r τ`. -/
theorem ownerRow_eq_and_label?_eq_some_iff {u : Carrier R C} {r : R} {τ : ι} :
    ownerRow u = r ∧ label? u = some τ ↔ ∃ x : C r τ, u = pt r τ x := by
  cases u with
  | row r' => simp
  | pt r' τ' x =>
    constructor
    · rintro ⟨rfl, hτ⟩
      obtain rfl : τ' = τ := Option.some.inj hτ
      exact ⟨x, rfl⟩
    · rintro ⟨x', h⟩
      exact ⟨by simpa using congrArg ownerRow h, by simpa using congrArg label? h⟩

/-- Equivalence identifying `Carrier R C` with the disjoint union of `R` and the sigma of all
fibers. -/
def equivSum : Carrier R C ≃ R ⊕ Σ r : R, Σ τ : ι, C r τ where
  toFun
    | row r => .inl r
    | pt r τ x => .inr ⟨r, τ, x⟩
  invFun
    | .inl r => row r
    | .inr ⟨r, τ, x⟩ => pt r τ x
  left_inv u := by cases u <;> rfl
  right_inv s := by rcases s with r | ⟨r, τ, x⟩ <;> rfl

@[simp]
theorem equivSum_row (r : R) : equivSum (row r : Carrier R C) = .inl r := (rfl)

@[simp]
theorem equivSum_pt (r : R) (τ : ι) (x : C r τ) :
    equivSum (pt r τ x) = .inr ⟨r, τ, x⟩ := (rfl)

@[simp]
theorem equivSum_symm_inl (r : R) :
    (equivSum (C := C)).symm (.inl r) = row r := (rfl)

@[simp]
theorem equivSum_symm_inr (r : R) (τ : ι) (x : C r τ) :
    (equivSum (C := C)).symm (.inr ⟨r, τ, x⟩) = pt r τ x := (rfl)

instance countable [Countable ι] [Countable R] [∀ r τ, Countable (C r τ)] :
    Countable (Carrier R C) :=
  Countable.of_equiv _ equivSum.symm

instance infinite [Infinite R] : Infinite (Carrier R C) :=
  Infinite.of_injective (row : R → Carrier R C) fun _ _ h => Carrier.row.inj h

end Carrier

/-! ### The `(lang ι Lc)`-structure on `Carrier R C` -/

section Structure

variable {ι : Type u} {Lc : Language.{u₁, v₁}}
variable {R : Type w₁} {C : R → ι → Type w₂} [∀ r τ, Lc.Structure (C r τ)]

/-- The canonical `(lang ι Lc)`-structure on `Carrier R C` induced by component `Lc`-structures on
each fiber `C r τ`. -/
instance instStructureCarrier : (lang ι Lc).Structure (Carrier R C) where
  funMap fn := isEmptyElim fn
  RelMap
    | .row, v => (v 0).label? = none
    | .own, v => (v 0).label? ≠ none ∧ (v 1).label? = none ∧ (v 0).ownerRow = (v 1).ownerRow
    | .lab τ, v => (v 0).label? = some τ
    | .lift rel, v => ∃ (r : R) (τ : ι) (xs : Fin _ → C r τ),
        (∀ i, v i = Carrier.pt r τ (xs i)) ∧ Structure.RelMap rel xs
    | .lift0 rel τ, v => ∃ r : R, v 0 = Carrier.row r ∧
        @Structure.RelMap Lc (C r τ) _ 0 rel Fin.elim0

@[simp]
theorem relMap_row_iff (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang ι Lc) Sym.row v ↔ (v 0).label? = none := (Iff.rfl)

@[simp]
theorem relMap_own_iff (v : Fin 2 → Carrier R C) :
    Structure.RelMap (L := lang ι Lc) Sym.own v ↔
      (v 0).label? ≠ none ∧ (v 1).label? = none ∧ (v 0).ownerRow = (v 1).ownerRow := (Iff.rfl)

@[simp]
theorem relMap_lab_iff (τ : ι) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang ι Lc) (Sym.lab τ) v ↔ (v 0).label? = some τ := (Iff.rfl)

@[simp]
theorem relMap_lift_iff {l : ℕ} (rel : Lc.Relations (l + 1)) (v : Fin (l + 1) → Carrier R C) :
    Structure.RelMap (L := lang ι Lc) (Sym.lift rel) v ↔
      ∃ (r : R) (τ : ι) (xs : Fin (l + 1) → C r τ),
        (∀ i, v i = Carrier.pt r τ (xs i)) ∧ Structure.RelMap rel xs := (Iff.rfl)

@[simp]
theorem relMap_lift0_iff (rel : Lc.Relations 0) (τ : ι) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang ι Lc) (Sym.lift0 rel τ) v ↔
      ∃ r : R, v 0 = Carrier.row r ∧ @Structure.RelMap Lc (C r τ) _ 0 rel Fin.elim0 := (Iff.rfl)

/-- Positive-arity lifted relations on a tuple of points in a single fiber `(r, τ)` reduce to the
component relation in `C r τ`. -/
theorem relMap_lift_pt_iff {l : ℕ} (rel : Lc.Relations (l + 1)) (r : R) (τ : ι)
    (xs : Fin (l + 1) → C r τ) :
    Structure.RelMap (L := lang ι Lc) (Sym.lift rel) (fun i => Carrier.pt r τ (xs i)) ↔
      Structure.RelMap rel xs := by
  rw [relMap_lift_iff]
  constructor
  · rintro ⟨r', τ', ys, hys, hR⟩
    have h0 := hys 0
    injection h0 with hr hτ _
    subst hr hτ
    have heq : ys = xs := funext fun i => (Carrier.pt_injective r τ (hys i)).symm
    exact heq ▸ hR
  · intro hR
    exact ⟨r, τ, xs, fun _ => rfl, hR⟩

/-- Nullary lifted relations at label `τ` read on `Carrier.row r` reduce to the nullary relation in
`C r τ`. -/
theorem relMap_lift0_row_iff (rel : Lc.Relations 0) (τ : ι) (r : R) :
    Structure.RelMap (L := lang ι Lc) (Sym.lift0 rel τ)
      (fun _ => Carrier.row r : Fin 1 → Carrier R C) ↔
      @Structure.RelMap Lc (C r τ) _ 0 rel Fin.elim0 := by
  simp

end Structure

/-! ### Isomorphism assembly and restriction -/

section Isomorphism

variable {ι : Type u} {Lc : Language.{u₁, v₁}}
variable {R₁ : Type w₁} {C₁ : R₁ → ι → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → ι → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

/-- Carrier equivalence assembled from a row bijection and fiber bijections. -/
private def equivCarrierOfFibers (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃ C₂ (σ r) τ) :
    Carrier R₁ C₁ ≃ Carrier R₂ C₂ :=
  Carrier.equivSum.trans
    ((Equiv.sumCongr σ
      (Equiv.sigmaCongr σ fun r => Equiv.sigmaCongrRight fun τ => f r τ)).trans
      Carrier.equivSum.symm)

@[simp]
private theorem equivCarrierOfFibers_row (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃ C₂ (σ r) τ)
    (r : R₁) : equivCarrierOfFibers σ f (.row r) = .row (σ r) := by
  simp [equivCarrierOfFibers]

@[simp]
private theorem equivCarrierOfFibers_pt (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃ C₂ (σ r) τ)
    (r : R₁) (τ : ι) (x : C₁ r τ) :
    equivCarrierOfFibers σ f (.pt r τ x) = .pt (σ r) τ (f r τ x) := by
  simp [equivCarrierOfFibers, Equiv.sigmaCongr]

private theorem label?_equivCarrierOfFibers (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃ C₂ (σ r) τ)
    (u : Carrier R₁ C₁) : (equivCarrierOfFibers σ f u).label? = u.label? := by
  cases u <;> simp

private theorem ownerRow_equivCarrierOfFibers (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃ C₂ (σ r) τ)
    (u : Carrier R₁ C₁) : (equivCarrierOfFibers σ f u).ownerRow = σ u.ownerRow := by
  cases u <;> simp

private theorem relMap_lift_equivCarrierOfFibers_iff (σ : R₁ ≃ R₂)
    (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) {l : ℕ} (rel : Lc.Relations (l + 1))
    (xs : Fin (l + 1) → Carrier R₁ C₁) :
    Structure.RelMap (L := lang ι Lc) (Sym.lift rel)
      (equivCarrierOfFibers σ (fun r τ => (f r τ).toEquiv) ∘ xs) ↔
      Structure.RelMap (L := lang ι Lc) (Sym.lift rel) xs := by
  simp only [relMap_lift_iff, Function.comp_apply]
  constructor
  · rintro ⟨r', τ, ys, hys, hR⟩
    obtain ⟨r, rfl⟩ := σ.surjective r'
    have hxs : ∀ i, ∃ x : C₁ r τ, xs i = .pt r τ x ∧ f r τ x = ys i := fun i => by
      have hi := hys i
      cases hxi : xs i with
      | row _ => simp [hxi] at hi
      | pt r₀ τ₀ x =>
        rw [hxi, equivCarrierOfFibers_pt] at hi
        injection hi with hr hτ hx
        obtain rfl := σ.injective hr
        obtain rfl := hτ
        exact ⟨x, rfl, eq_of_heq hx⟩
    choose g hg₁ hg₂ using hxs
    refine ⟨r, τ, g, hg₁, ((f r τ).map_rel rel g).mp ?_⟩
    have hfg : f r τ ∘ g = ys := funext hg₂
    rwa [hfg]
  · rintro ⟨r, τ, gs, hgs, hR⟩
    exact ⟨σ r, τ, f r τ ∘ gs, fun i => by rw [hgs i, equivCarrierOfFibers_pt]; rfl,
      ((f r τ).map_rel rel gs).mpr hR⟩

private theorem map_rel_equivCarrierOfFibers (σ : R₁ ≃ R₂)
    (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) {n : ℕ} (s : Sym ι Lc n)
    (xs : Fin n → Carrier R₁ C₁) :
    Structure.RelMap (L := lang ι Lc) s
      (equivCarrierOfFibers σ (fun r τ => (f r τ).toEquiv) ∘ xs) ↔
      Structure.RelMap (L := lang ι Lc) s xs := by
  cases s with
  | row => simp [label?_equivCarrierOfFibers]
  | own => simp [label?_equivCarrierOfFibers, ownerRow_equivCarrierOfFibers, σ.injective.eq_iff]
  | lab τ => simp [label?_equivCarrierOfFibers]
  | lift rel => exact relMap_lift_equivCarrierOfFibers_iff σ f rel xs
  | lift0 rel τ =>
    simp only [relMap_lift0_iff, Function.comp_apply]
    constructor
    · rintro ⟨r', hr', hR⟩
      obtain ⟨r, rfl⟩ := σ.surjective r'
      cases h0 : xs 0 with
      | pt _ _ _ => simp [h0] at hr'
      | row r₀ =>
        rw [h0, equivCarrierOfFibers_row] at hr'
        obtain rfl := σ.injective (Carrier.row.inj hr')
        refine ⟨r₀, rfl, ((f r₀ τ).map_rel rel Fin.elim0).mp ?_⟩
        rwa [Subsingleton.elim (f r₀ τ ∘ Fin.elim0) Fin.elim0]
    · rintro ⟨r, hr, hR⟩
      refine ⟨σ r, by simp [hr], ?_⟩
      have hR' := ((f r τ).map_rel rel Fin.elim0).mpr hR
      rwa [Subsingleton.elim (f r τ ∘ Fin.elim0) Fin.elim0] at hR'

/-- Assemble an isomorphism of row assemblies from a bijection of rows and a family of component
`Lc`-isomorphisms on all fibers. -/
def equivOfFibers (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) :
    Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂ where
  toEquiv := equivCarrierOfFibers σ fun r τ => (f r τ).toEquiv
  map_fun' {_} fn _ := isEmptyElim fn
  map_rel' {_} s xs := map_rel_equivCarrierOfFibers σ f s xs

@[simp]
theorem equivOfFibers_row (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) (r : R₁) :
    equivOfFibers σ f (.row r) = .row (σ r) :=
  equivCarrierOfFibers_row σ (fun r τ => (f r τ).toEquiv) r

@[simp]
theorem equivOfFibers_pt (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) (r : R₁)
    (τ : ι) (x : C₁ r τ) :
    equivOfFibers σ f (.pt r τ x) = .pt (σ r) τ (f r τ x) :=
  equivCarrierOfFibers_pt σ (fun r τ => (f r τ).toEquiv) r τ x

@[simp]
theorem equivOfFibers_symm_row (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) (r : R₂) :
    (equivOfFibers σ f).symm (.row r) = .row (σ.symm r) :=
  (equivOfFibers σ f).injective (by simp)

@[simp]
theorem equivOfFibers_symm_pt (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) (r : R₁)
    (τ : ι) (y : C₂ (σ r) τ) :
    (equivOfFibers σ f).symm (.pt (σ r) τ y) = .pt r τ ((f r τ).symm y) :=
  (equivOfFibers σ f).injective (by simp)

end Isomorphism

end TauCeti.RowAssembly

namespace FirstOrder.Language.Equiv

open TauCeti.RowAssembly FirstOrder FirstOrder.Language

section RowAssembly

variable {ι : Type u} {Lc : Language.{u₁, v₁}}
variable {R₁ : Type w₁} {C₁ : R₁ → ι → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → ι → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

/-- Every `(lang ι Lc)`-isomorphism preserves optional fiber labels (`none` on rows and `some τ`
on points of label `τ`). -/
@[simp]
theorem label?_apply (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (u : Carrier R₁ C₁) :
    (e u).label? = u.label? := by
  cases hl : u.label? with
  | none =>
    exact (relMap_row_iff _).mp ((e.map_rel Sym.row (fun _ => u)).mpr ((relMap_row_iff _).mpr hl))
  | some τ =>
    exact (relMap_lab_iff τ _).mp
      ((e.map_rel (Sym.lab τ) (fun _ => u)).mpr ((relMap_lab_iff τ _).mpr hl))

/-- Forward row map extracted from an isomorphism of row assemblies. -/
private def rowMap (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁) : R₂ :=
  (e (.row r)).ownerRow

private theorem apply_row_eq (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁) :
    e (.row r) = .row (rowMap e r) := by
  apply Carrier.label?_eq_none_iff.mp
  simp

/-- The bijection of rows induced by an isomorphism of row assemblies. -/
def rowEquiv (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) : R₁ ≃ R₂ where
  toFun := rowMap e
  invFun := rowMap e.symm
  left_inv r := by
    have h := congrArg Carrier.ownerRow (e.symm_apply_apply (.row r))
    rw [apply_row_eq e r, apply_row_eq e.symm (rowMap e r)] at h
    exact h
  right_inv r' := by
    have h := congrArg Carrier.ownerRow (e.apply_symm_apply (.row r'))
    rw [apply_row_eq e.symm r', apply_row_eq e (rowMap e.symm r')] at h
    exact h

/-- Action of a `(lang ι Lc)`-isomorphism on a row element via `rowEquiv`. The `simp` priority is
`low` so specialized evaluation lemmas such as `equivOfFibers_row`, `equivOfFibers_symm_row`, and
`FirstOrder.Language.Equiv.refl_apply` (as well as local hypotheses) fire first. -/
@[simp low]
theorem apply_row (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁) :
    e (.row r) = .row (e.rowEquiv r) :=
  apply_row_eq e r

@[simp]
theorem rowEquiv_symm (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) :
    e.symm.rowEquiv = e.rowEquiv.symm := (rfl)

/-- Every `(lang ι Lc)`-isomorphism commutes with `ownerRow` via `rowEquiv`. -/
@[simp]
theorem ownerRow_apply (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (u : Carrier R₁ C₁) :
    (e u).ownerRow = e.rowEquiv u.ownerRow := by
  cases u with
  | row r => simp
  | pt r τ x =>
    let v : Fin 2 → Carrier R₁ C₁ := Fin.cons (.pt r τ x) (fun _ => .row r)
    have hown : Structure.RelMap (L := lang ι Lc) Sym.own v := by simp [v]
    have hown' := (e.map_rel Sym.own v).mpr hown
    simp only [relMap_own_iff, Function.comp_apply, v, Fin.cons_zero, Fin.cons_one,
      apply_row, Carrier.ownerRow_row] at hown'
    exact hown'.2.2

private theorem exists_pt_apply (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) (x : C₁ r τ) :
    ∃ y : C₂ (e.rowEquiv r) τ, e (.pt r τ x) = .pt (e.rowEquiv r) τ y :=
  Carrier.ownerRow_eq_and_label?_eq_some_iff.mp ⟨by simp, by simp⟩

/-- Forward fiber map extracted from an isomorphism of row assemblies. -/
private noncomputable def fiberMap (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) (x : C₁ r τ) : C₂ (e.rowEquiv r) τ :=
  (exists_pt_apply e r τ x).choose

private theorem apply_pt_eq (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) (x : C₁ r τ) :
    e (.pt r τ x) = .pt (e.rowEquiv r) τ (fiberMap e r τ x) :=
  (exists_pt_apply e r τ x).choose_spec

private theorem bijective_fiberMap (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) : Function.Bijective (fiberMap e r τ) := by
  refine ⟨fun x₁ x₂ h => ?_, fun y => ?_⟩
  · apply Carrier.pt_injective r τ
    apply e.injective
    rw [apply_pt_eq, apply_pt_eq, h]
  · let u : Carrier R₁ C₁ := e.symm (.pt (e.rowEquiv r) τ y)
    have ho : u.ownerRow = r := by simp [u]
    have hl : u.label? = some τ := by simp [u]
    obtain ⟨x, hx⟩ := Carrier.ownerRow_eq_and_label?_eq_some_iff.mp ⟨ho, hl⟩
    refine ⟨x, Carrier.pt_injective (e.rowEquiv r) τ ?_⟩
    rw [← apply_pt_eq, ← hx]
    exact e.apply_symm_apply _

/-- The bijection on a single fiber `(r, τ)` induced by an isomorphism of row assemblies. The
component language `Lc` need not be relational for the bare bijection. -/
noncomputable def fiberToEquiv (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁) (τ : ι) :
    C₁ r τ ≃ C₂ (e.rowEquiv r) τ :=
  Equiv.ofBijective (fiberMap e r τ) (bijective_fiberMap e r τ)

/-- Action of a `(lang ι Lc)`-isomorphism on a fiber point via `rowEquiv` and `fiberToEquiv`.
Intentionally not `@[simp]`: because `Carrier.pt` depends on the row index, eager rewriting of
`e (.pt r τ x)` breaks bottom-up `simp` on `FirstOrder.Language.Equiv.symm_apply_apply`,
`apply_symm_apply`, and `EmbeddingLike.apply_eq_iff_eq`, leaving stuck `HEq` goals. -/
theorem apply_pt_eq_pt_fiberToEquiv (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) (x : C₁ r τ) :
    e (.pt r τ x) = .pt (e.rowEquiv r) τ (e.fiberToEquiv r τ x) :=
  apply_pt_eq e r τ x

private theorem map_rel_fiberToEquiv (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) {n : ℕ} (rel : Lc.Relations n) (xs : Fin n → C₁ r τ) :
    Structure.RelMap rel (e.fiberToEquiv r τ ∘ xs) ↔ Structure.RelMap rel xs := by
  cases n with
  | zero =>
    have h := e.map_rel (Sym.lift0 rel τ) (fun _ => .row r)
    simp only [relMap_lift0_iff, Function.comp_apply, apply_row, Carrier.row.injEq,
      exists_eq_left'] at h
    rwa [Subsingleton.elim (e.fiberToEquiv r τ ∘ xs) Fin.elim0, Subsingleton.elim xs Fin.elim0]
  | succ l =>
    let v : Fin (l + 1) → Carrier R₁ C₁ := fun i => .pt r τ (xs i)
    have h := e.map_rel (Sym.lift rel) v
    have hv : e ∘ v = fun i => .pt (e.rowEquiv r) τ (e.fiberToEquiv r τ (xs i)) :=
      funext fun i => e.apply_pt_eq_pt_fiberToEquiv r τ (xs i)
    rwa [hv, relMap_lift_pt_iff, relMap_lift_pt_iff] at h

/-- When the component language `Lc` is relational, the fiber bijection induced by an isomorphism
of row assemblies is an `Lc`-isomorphism on every fiber. -/
noncomputable def fiberEquiv [Lc.IsRelational] (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂)
    (r : R₁) (τ : ι) : C₁ r τ ≃[Lc] C₂ (e.rowEquiv r) τ where
  toEquiv := e.fiberToEquiv r τ
  map_fun' {_} fn _ := isEmptyElim fn
  map_rel' {_} rel xs := map_rel_fiberToEquiv e r τ rel xs

@[simp]
theorem toEquiv_fiberEquiv [Lc.IsRelational] (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂)
    (r : R₁) (τ : ι) :
    (e.fiberEquiv r τ).toEquiv = e.fiberToEquiv r τ := (rfl)

theorem coe_fiberEquiv [Lc.IsRelational] (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂)
    (r : R₁) (τ : ι) :
    ⇑(e.fiberEquiv r τ) = e.fiberToEquiv r τ := (rfl)

/-- Action of a `(lang ι Lc)`-isomorphism on a fiber point via `rowEquiv` and `fiberEquiv`. -/
theorem apply_pt [Lc.IsRelational] (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) (r : R₁)
    (τ : ι) (x : C₁ r τ) :
    e (.pt r τ x) = .pt (e.rowEquiv r) τ (e.fiberEquiv r τ x) :=
  e.apply_pt_eq_pt_fiberToEquiv r τ x

/-- Reassembling the restricted row bijection and fiber isomorphisms recovers the original
isomorphism of row assemblies. -/
@[simp]
theorem equivOfFibers_rowEquiv_fiberEquiv [Lc.IsRelational]
    (e : Carrier R₁ C₁ ≃[lang ι Lc] Carrier R₂ C₂) :
    equivOfFibers e.rowEquiv e.fiberEquiv = e := by
  ext u
  cases u with
  | row r => exact (e.apply_row r).symm
  | pt r τ x => exact (e.apply_pt r τ x).symm

end RowAssembly

end FirstOrder.Language.Equiv

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language

section RowEquivOfFibers

variable {ι : Type u} {Lc : Language.{u₁, v₁}}
variable {R₁ : Type w₁} {C₁ : R₁ → ι → Type w₂} [∀ r τ, Lc.Structure (C₁ r τ)]
variable {R₂ : Type w₁'} {C₂ : R₂ → ι → Type w₂'} [∀ r τ, Lc.Structure (C₂ r τ)]

@[simp]
theorem rowEquiv_equivOfFibers (σ : R₁ ≃ R₂) (f : ∀ r τ, C₁ r τ ≃[Lc] C₂ (σ r) τ) :
    (equivOfFibers σ f).rowEquiv = σ := by
  ext r
  have h := (equivOfFibers σ f).apply_row r
  rw [equivOfFibers_row] at h
  exact (Carrier.row.inj h).symm

end RowEquivOfFibers

end TauCeti.RowAssembly
