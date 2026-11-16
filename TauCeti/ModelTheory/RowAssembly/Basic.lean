/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.List

/-!
# Row assemblies of relational structures

A *row assembly* combines a family of `Lc`-structures `C r τ`, indexed by a type `R` of *rows*
and nonempty words `τ : Label U` over an alphabet `U`, into a single relational structure in
`lang U Lc`. Its carrier `Carrier R C` consists of one marker element `.row r` per row and the
disjoint union of the fibers `C r τ` as elements `.pt r τ x`.

The assembled language `lang U Lc` has unary predicates `row` and `lab τ` selecting the rows and
the points of label `τ`, a binary ownership predicate `own` pairing each point `.pt r τ x` with
its owner row `.row r`, a lifted `(l + 1)`-ary symbol `lift R` evaluating each positive-arity
relation `R` of `Lc` inside every fiber, and a unary symbol `lift0 R τ` reading each nullary
relation `R` of `Lc` on fiber `(r, τ)` at `.row r`.

When `Lc` is relational, isomorphisms of row assemblies correspond precisely to bijections of rows
accompanied by fiberwise `Lc`-isomorphisms: every assembly isomorphism restricts to a row
bijection `rowEquiv e` and fiber isomorphisms `fiberEquiv e r τ`, and conversely any row bijection
together with fiber isomorphisms assembles into `equivOfFiberEquiv`. When `Lc = Language.empty`,
every permutation of the carrier that preserves `Carrier.slot` is an automorphism.

## Main definitions

* `TauCeti.RowAssembly.Label`: nonempty words over an alphabet `U`.
* `TauCeti.RowAssembly.Sym` and `TauCeti.RowAssembly.lang`: the assembled relational language.
* `TauCeti.RowAssembly.Carrier`: the assembled carrier with row markers and fiber points, together
  with its canonical `lang U Lc`-structure.
* `TauCeti.RowAssembly.equivOfFiberEquiv` and `TauCeti.RowAssembly.equivOfSlotPerm`: assembly of
  isomorphisms from fiber isomorphisms or slot-preserving permutations.
* `TauCeti.RowAssembly.rowEquiv` and `TauCeti.RowAssembly.fiberEquiv`: restriction of an assembly
  isomorphism to the rows and to each fiber.

## Main results

* `TauCeti.RowAssembly.nonempty_equiv_iff`: two row assemblies over a relational component language
  are isomorphic exactly when there is a bijection of rows along which corresponding fibers are
  isomorphic.

## References

Adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/ModelTheory/FiberAssembly.lean` and
`InfinitaryLogic/ModelTheory/FiberIsoAssembly.lean` (checkpoint
`518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0).
-/

public section

universe u u' v' w w' w₁ w₂ w₁' w₂'

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

/-- Labels: nonempty words over an alphabet `U`. -/
abbrev Label (U : Type u) : Type u := {τ : List U // τ ≠ []}

/-- The relation symbols of the assembled language: rows, ownership, labels, and the lifted
component relations (with nullary ones read at the owner row). -/
inductive Sym (U : Type u) (Lc : Language.{u', v'}) : ℕ → Type (max u v')
  | row : Sym U Lc 1
  | own : Sym U Lc 2
  | lab (τ : Label U) : Sym U Lc 1
  | lift {l : ℕ} (R : Lc.Relations (l + 1)) : Sym U Lc (l + 1)
  | lift0 (R : Lc.Relations 0) (τ : Label U) : Sym U Lc 1

/-- The assembled relational language over alphabet `U` and component language `Lc`. -/
@[expose] def lang (U : Type u) (Lc : Language.{u', v'}) : Language.{0, max u v'} :=
  ⟨fun _ => PEmpty, Sym U Lc⟩

instance (U : Type u) (Lc : Language.{u', v'}) : (lang U Lc).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty PEmpty)

instance {U : Type u} {Lc : Language.{u', v'}} {n : ℕ}
    [Countable U] [Countable (Lc.Relations 0)] [Countable (Lc.Relations n)] :
    Countable (Sym U Lc n) := by
  let f : Sym U Lc n →
      Unit ⊕ Unit ⊕ Label U ⊕ Lc.Relations n ⊕ (Lc.Relations 0 × Label U)
    | .row => .inl ()
    | .own => .inr (.inl ())
    | .lab τ => .inr (.inr (.inl τ))
    | .lift R => .inr (.inr (.inr (.inl R)))
    | .lift0 R τ => .inr (.inr (.inr (.inr (R, τ))))
  refine Function.Injective.countable (f := f) fun a b h => ?_
  cases a <;> cases b <;> simp_all [f]

instance {U : Type u} {Lc : Language.{u', v'}} {n : ℕ}
    [Countable U] [Countable (Lc.Relations 0)] [Countable (Lc.Relations n)] :
    Countable ((lang U Lc).Relations n) :=
  inferInstanceAs (Countable (Sym U Lc n))

/-- The assembled carrier: one marker `.row r` for each row `r`, and one point `.pt r τ x` for
each element `x` of the fiber `C r τ`. -/
inductive Carrier {U : Type u} (R : Type w) (C : R → Label U → Type w') :
    Type (max u w w')
  | row (r : R)
  | pt (r : R) (τ : Label U) (x : C r τ)

namespace Carrier

variable {U : Type u} {R : Type w} {C : R → Label U → Type w'}

/-- Two points in the same fiber are equal exactly when their fiber elements are equal. -/
theorem pt_inj_iff {r : R} {τ : Label U} {x y : C r τ} :
    (Carrier.pt r τ x : Carrier R C) = Carrier.pt r τ y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    rfl

/-- The row owning a carrier element (a row owns itself). -/
def ownerRow : Carrier R C → R
  | .row r => r
  | .pt r _ _ => r

@[simp]
theorem ownerRow_row (r : R) : (Carrier.row (C := C) r).ownerRow = r := (rfl)

@[simp]
theorem ownerRow_pt (r : R) (τ : Label U) (x : C r τ) :
    (Carrier.pt r τ x).ownerRow = r := (rfl)

/-- The slot of a carrier element: either a row marker `Sum.inl r` or a fiber address
`Sum.inr (r, τ)`. -/
def slot : Carrier R C → R ⊕ (R × Label U)
  | .row r => .inl r
  | .pt r τ _ => .inr (r, τ)

@[simp]
theorem slot_row (r : R) : (Carrier.row (C := C) r).slot = .inl r := (rfl)

@[simp]
theorem slot_pt (r : R) (τ : Label U) (x : C r τ) :
    (Carrier.pt r τ x).slot = .inr (r, τ) := (rfl)

/-- An element whose slot is `Sum.inl r` is the row marker `.row r`. -/
theorem eq_row_of_slot_eq_inl {a : Carrier R C} {r : R} (h : a.slot = .inl r) :
    a = .row r := by
  cases a with
  | row r' =>
    simp only [slot_row, Sum.inl.injEq] at h
    exact congrArg Carrier.row h
  | pt _ _ _ => simp at h

/-- An element whose slot is `Sum.inr (r, τ)` is a point of the fiber `C r τ`. -/
theorem exists_pt_of_slot_eq_inr {a : Carrier R C} {r : R} {τ : Label U}
    (h : a.slot = .inr (r, τ)) : ∃ x : C r τ, a = .pt r τ x := by
  cases a with
  | row _ => simp at h
  | pt r' τ' x =>
    simp only [slot_pt, Sum.inr.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨x, rfl⟩

instance [Countable U] [Countable R] [∀ r τ, Countable (C r τ)] :
    Countable (Carrier R C) := by
  let f : Carrier R C → R ⊕ (Σ r : R, Σ τ : Label U, C r τ)
    | .row r => .inl r
    | .pt r τ x => .inr ⟨r, τ, x⟩
  refine Function.Injective.countable (f := f) fun a b h => ?_
  cases a <;> cases b <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · exact congrArg Carrier.row h
  · rcases Sigma.mk.inj_iff.mp h with ⟨rfl, h⟩
    cases h
    rfl

instance [Infinite R] : Infinite (Carrier R C) :=
  Infinite.of_injective Carrier.row fun _ _ h => Carrier.row.inj h

instance [Nonempty R] : Nonempty (Carrier R C) :=
  let ⟨r⟩ := ‹Nonempty R›
  ⟨.row r⟩

end Carrier

section Structure

variable {U : Type u} {Lc : Language.{u', v'}} {R : Type w} {C : R → Label U → Type w'}
variable [∀ r τ, Lc.Structure (C r τ)]

/-- The canonical `lang U Lc`-structure on `Carrier R C`. -/
instance instStructure : (lang U Lc).Structure (Carrier R C) where
  funMap f := PEmpty.elim f
  RelMap {n} s v :=
    match s, v with
    | .row, v => ∃ r, v 0 = .row r
    | .own, v => ∃ r τ x, v 0 = .pt r τ x ∧ v 1 = .row r
    | .lab τ, v => ∃ r x, v 0 = .pt r τ x
    | .lift S, v =>
        ∃ r τ, ∃ x : Fin _ → C r τ, (∀ i, v i = .pt r τ (x i)) ∧ RelMap S x
    | .lift0 S τ, v =>
        ∃ r, v 0 = .row r ∧ @RelMap Lc (C r τ) _ 0 S Fin.elim0

@[simp]
theorem relMap_row_iff (v : Fin 1 → Carrier R C) :
    RelMap (L := lang U Lc) (.row : Sym U Lc 1) v ↔ ∃ r, v 0 = .row r := Iff.rfl

@[simp]
theorem relMap_own_iff (v : Fin 2 → Carrier R C) :
    RelMap (L := lang U Lc) (.own : Sym U Lc 2) v ↔
      ∃ r τ x, v 0 = .pt r τ x ∧ v 1 = .row r := Iff.rfl

@[simp]
theorem relMap_lab_iff (τ : Label U) (v : Fin 1 → Carrier R C) :
    RelMap (L := lang U Lc) (.lab τ : Sym U Lc 1) v ↔ ∃ r x, v 0 = .pt r τ x := Iff.rfl

@[simp]
theorem relMap_lift_iff {l : ℕ} (S : Lc.Relations (l + 1))
    (v : Fin (l + 1) → Carrier R C) :
    RelMap (L := lang U Lc) (.lift S : Sym U Lc (l + 1)) v ↔
      ∃ r τ, ∃ x : Fin (l + 1) → C r τ,
        (∀ i, v i = .pt r τ (x i)) ∧ RelMap S x := Iff.rfl

@[simp]
theorem relMap_lift0_iff (S : Lc.Relations 0) (τ : Label U) (v : Fin 1 → Carrier R C) :
    RelMap (L := lang U Lc) (.lift0 S τ : Sym U Lc 1) v ↔
      ∃ r, v 0 = .row r ∧ @RelMap Lc (C r τ) _ 0 S Fin.elim0 := Iff.rfl

theorem relMap_lift_pt_iff {l : ℕ} (S : Lc.Relations (l + 1)) (r : R) (τ : Label U)
    (x : Fin (l + 1) → C r τ) :
    RelMap (L := lang U Lc) (.lift S : Sym U Lc (l + 1))
      (fun i => (Carrier.pt r τ (x i) : Carrier R C)) ↔ RelMap (L := Lc) S x := by
  refine ⟨fun hS => ?_, fun hS => ⟨r, τ, x, fun _ => rfl, hS⟩⟩
  obtain ⟨r', τ', y, hy, hSy⟩ := (relMap_lift_iff _ _).mp hS
  have hslot := congrArg Carrier.slot (hy 0)
  simp only [Carrier.slot_pt, Sum.inr.injEq, Prod.mk.injEq] at hslot
  rcases hslot with ⟨rfl, rfl⟩
  have hyx : y = x := funext fun i => (Carrier.pt_inj_iff.mp (hy i)).symm
  exact hyx ▸ hSy

theorem relMap_lift0_row_iff (S : Lc.Relations 0) (τ : Label U) (r : R) :
    RelMap (L := lang U Lc) (.lift0 S τ : Sym U Lc 1) (![Carrier.row (C := C) r]) ↔
      @RelMap Lc (C r τ) _ 0 S Fin.elim0 := by
  simp only [relMap_lift0_iff, Matrix.cons_val_zero, Carrier.row.injEq, exists_eq_left']

end Structure

/-! ### Isomorphism assembly -/

section EquivAssembly

variable {U : Type u} {Lc : Language.{u', v'}}
variable {R₁ : Type w₁} {R₂ : Type w₂}
variable {C₁ : R₁ → Label U → Type w₁'} {C₂ : R₂ → Label U → Type w₂'}
variable [∀ r τ, Lc.Structure (C₁ r τ)] [∀ r τ, Lc.Structure (C₂ r τ)]

/-- Underlying bijection of `equivOfFiberEquiv`. -/
private def carrierEquivOfFiberEquiv (eR : R₁ ≃ R₂)
    (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) :
    Carrier R₁ C₁ ≃ Carrier R₂ C₂ where
  toFun
    | .row r => .row (eR r)
    | .pt r τ x => .pt (eR r) τ (eF r τ x)
  invFun
    | .row r => .row (eR.symm r)
    | .pt r τ y =>
        .pt (eR.symm r) τ ((eF (eR.symm r) τ).symm ((eR.apply_symm_apply r).symm ▸ y))
  left_inv
    | .row r => by simp
    | .pt r τ x => by
      dsimp only
      have aux : ∀ (r' : R₁) (heq : eR r' = eR r),
          Carrier.pt r' τ ((eF r' τ).symm (heq.symm ▸ eF r τ x)) = Carrier.pt r τ x := by
        rintro r' heq
        obtain rfl : r' = r := eR.injective heq
        simp
      exact aux (eR.symm (eR r)) (eR.apply_symm_apply (eR r))
  right_inv
    | .row r => by simp
    | .pt r τ y => by
      dsimp only
      obtain ⟨r₁, rfl⟩ := eR.surjective r
      have aux : ∀ (r' : R₁) (heq : eR r' = eR r₁),
          Carrier.pt (eR r') τ (eF r' τ ((eF r' τ).symm (heq.symm ▸ y))) =
            Carrier.pt (eR r₁) τ y := by
        rintro r' heq
        obtain rfl : r' = r₁ := eR.injective heq
        simp
      exact aux (eR.symm (eR r₁)) (eR.apply_symm_apply (eR r₁))

/-- Forward preservation of relations under `carrierEquivOfFiberEquiv`. -/
private theorem relMap_carrierEquiv_of_rel (eR : R₁ ≃ R₂)
    (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) {n : ℕ} (s : Sym U Lc n)
    (v : Fin n → Carrier R₁ C₁) (hv : RelMap (L := lang U Lc) s v) :
    RelMap (L := lang U Lc) s (carrierEquivOfFiberEquiv eR eF ∘ v) := by
  cases s with
  | row =>
    obtain ⟨r₁, hr⟩ := (relMap_row_iff _).mp hv
    exact ⟨eR r₁, by simp [Function.comp_apply, hr, carrierEquivOfFiberEquiv]⟩
  | own =>
    obtain ⟨r₁, τ, x, h0, h1⟩ := (relMap_own_iff _).mp hv
    exact ⟨eR r₁, τ, eF r₁ τ x, by simp [Function.comp_apply, h0, carrierEquivOfFiberEquiv],
      by simp [Function.comp_apply, h1, carrierEquivOfFiberEquiv]⟩
  | lab τ =>
    obtain ⟨r₁, x, h0⟩ := (relMap_lab_iff _ _).mp hv
    exact ⟨eR r₁, eF r₁ τ x, by simp [Function.comp_apply, h0, carrierEquivOfFiberEquiv]⟩
  | lift R =>
    obtain ⟨r₁, τ, x, hv', hR⟩ := (relMap_lift_iff _ _).mp hv
    refine ⟨eR r₁, τ, fun i => eF r₁ τ (x i),
      fun i => by simp [Function.comp_apply, hv' i, carrierEquivOfFiberEquiv],
      ((eF r₁ τ).map_rel R x).mpr hR⟩
  | lift0 R τ =>
    obtain ⟨r₁, h0, hR⟩ := (relMap_lift0_iff _ _ _).mp hv
    refine ⟨eR r₁, by simp [Function.comp_apply, h0, carrierEquivOfFiberEquiv], ?_⟩
    have h := ((eF r₁ τ).map_rel R Fin.elim0).mpr hR
    simpa only [Subsingleton.elim ((eF r₁ τ) ∘ Fin.elim0) Fin.elim0] using h

/-- Backward reflection of relations under `carrierEquivOfFiberEquiv`. -/
private theorem rel_of_relMap_carrierEquiv (eR : R₁ ≃ R₂)
    (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) {n : ℕ} (s : Sym U Lc n)
    (v : Fin n → Carrier R₁ C₁)
    (hv : RelMap (L := lang U Lc) s (carrierEquivOfFiberEquiv eR eF ∘ v)) :
    RelMap (L := lang U Lc) s v := by
  let e := carrierEquivOfFiberEquiv eR eF
  cases s with
  | row =>
    obtain ⟨r₂, hr⟩ := (relMap_row_iff _).mp hv
    exact ⟨eR.symm r₂, e.injective (hr.trans (by simp [e, carrierEquivOfFiberEquiv]))⟩
  | own =>
    obtain ⟨r₂, τ, y, h0, h1⟩ := (relMap_own_iff _).mp hv
    obtain ⟨r₁, rfl⟩ := eR.surjective r₂
    exact ⟨r₁, τ, (eF r₁ τ).symm y,
      e.injective (h0.trans (by simp [e, carrierEquivOfFiberEquiv])),
      e.injective (h1.trans rfl)⟩
  | lab τ =>
    obtain ⟨r₂, y, h0⟩ := (relMap_lab_iff _ _).mp hv
    obtain ⟨r₁, rfl⟩ := eR.surjective r₂
    exact ⟨r₁, (eF r₁ τ).symm y,
      e.injective (h0.trans (by simp [e, carrierEquivOfFiberEquiv]))⟩
  | lift R =>
    obtain ⟨r₂, τ, y, hv', hR⟩ := (relMap_lift_iff _ _).mp hv
    obtain ⟨r₁, rfl⟩ := eR.surjective r₂
    refine ⟨r₁, τ, fun i => (eF r₁ τ).symm (y i),
      fun i => e.injective ((hv' i).trans (by simp [e, carrierEquivOfFiberEquiv])),
      ((eF r₁ τ).symm.map_rel R y).mpr hR⟩
  | lift0 R τ =>
    obtain ⟨r₂, h0, hR⟩ := (relMap_lift0_iff _ _ _).mp hv
    obtain ⟨r₁, rfl⟩ := eR.surjective r₂
    refine ⟨r₁, e.injective (h0.trans rfl), ?_⟩
    have h := ((eF r₁ τ).map_rel R Fin.elim0).mp
    rw [Subsingleton.elim ((eF r₁ τ) ∘ Fin.elim0) Fin.elim0] at h
    exact h hR

/-- **Isomorphism assembly.** A bijection of rows together with fiberwise `Lc`-isomorphisms
assembles into an isomorphism of row assemblies. -/
def equivOfFiberEquiv (eR : R₁ ≃ R₂) (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) :
    Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂ where
  toEquiv := carrierEquivOfFiberEquiv eR eF
  map_fun' f := PEmpty.elim f
  map_rel' {n} s v := by
    simp only [Equiv.toFun_as_coe]
    exact ⟨rel_of_relMap_carrierEquiv eR eF s v, relMap_carrierEquiv_of_rel eR eF s v⟩

theorem equivOfFiberEquiv_row (eR : R₁ ≃ R₂)
    (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) (r : R₁) :
    equivOfFiberEquiv eR eF (.row r) = .row (eR r) := (rfl)

@[simp]
theorem equivOfFiberEquiv_pt (eR : R₁ ≃ R₂) (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ)
    (r : R₁) (τ : Label U) (x : C₁ r τ) :
    equivOfFiberEquiv eR eF (.pt r τ x) = .pt (eR r) τ (eF r τ x) := (rfl)

/-- Over `Language.empty`, any slot-preserving self-map preserves every relation of
`lang U Language.empty`. -/
private theorem relMap_of_slot_eq {R : Type w} {C : R → Label U → Type w'}
    [∀ r τ, Language.empty.Structure (C r τ)] {f : Carrier R C → Carrier R C}
    (hf : ∀ x, (f x).slot = x.slot) {n : ℕ} (s : Sym U Language.empty n)
    (v : Fin n → Carrier R C) (hv : RelMap (L := lang U Language.empty) s v) :
    RelMap (L := lang U Language.empty) s (f ∘ v) := by
  cases s with
  | row =>
    obtain ⟨r, hr⟩ := (relMap_row_iff _).mp hv
    exact ⟨r, Carrier.eq_row_of_slot_eq_inl ((hf (v 0)).trans (by simp [hr]))⟩
  | own =>
    obtain ⟨r, τ, x, h0, h1⟩ := (relMap_own_iff _).mp hv
    obtain ⟨y, hy⟩ := Carrier.exists_pt_of_slot_eq_inr (r := r) (τ := τ)
      ((hf (v 0)).trans (by simp [h0]))
    exact ⟨r, τ, y, hy, Carrier.eq_row_of_slot_eq_inl ((hf (v 1)).trans (by simp [h1]))⟩
  | lab τ =>
    obtain ⟨r, x, h0⟩ := (relMap_lab_iff _ _).mp hv
    obtain ⟨y, hy⟩ := Carrier.exists_pt_of_slot_eq_inr (r := r) (τ := τ)
      ((hf (v 0)).trans (by simp [h0]))
    exact ⟨r, y, hy⟩
  | lift R => exact Empty.elim R
  | lift0 R _ => exact Empty.elim R

/-- Over the empty component language, every permutation of a row-assembly carrier that preserves
`Carrier.slot` is an automorphism of the assembly. -/
def equivOfSlotPerm {R : Type w} {C : R → Label U → Type w'}
    [∀ r τ, Language.empty.Structure (C r τ)] (σ : Equiv.Perm (Carrier R C))
    (hσ : ∀ x, (σ x).slot = x.slot) :
    Carrier R C ≃[lang U Language.empty] Carrier R C where
  toEquiv := σ
  map_fun' f := PEmpty.elim f
  map_rel' {n} s v := by
    simp only [Equiv.toFun_as_coe]
    have hσ' : ∀ x, (σ.symm x).slot = x.slot := fun x => by
      simpa using (hσ (σ.symm x)).symm
    refine ⟨fun h => ?_, fun h => relMap_of_slot_eq hσ s v h⟩
    have h' := relMap_of_slot_eq hσ' s (σ ∘ v) h
    have hcomp : (⇑σ.symm : Carrier R C → Carrier R C) ∘ (⇑σ ∘ v) = v := by
      funext i
      exact σ.symm_apply_apply (v i)
    rwa [hcomp] at h'

@[simp]
theorem equivOfSlotPerm_apply {R : Type w} {C : R → Label U → Type w'}
    [∀ r τ, Language.empty.Structure (C r τ)] (σ : Equiv.Perm (Carrier R C))
    (hσ : ∀ x, (σ x).slot = x.slot) (x : Carrier R C) :
    equivOfSlotPerm σ hσ x = σ x := (rfl)

end EquivAssembly

/-! ### Isomorphism restriction -/

section EquivRestriction

variable {U : Type u} {Lc : Language.{u', v'}}
variable {R₁ : Type w₁} {R₂ : Type w₂}
variable {C₁ : R₁ → Label U → Type w₁'} {C₂ : R₂ → Label U → Type w₂'}
variable [∀ r τ, Lc.Structure (C₁ r τ)] [∀ r τ, Lc.Structure (C₂ r τ)]

/-- An assembly isomorphism sends each row marker to a row marker. -/
private theorem exists_apply_row
    (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) (r : R₁) :
    ∃ r' : R₂, e (.row r) = .row r' := by
  have h := (e.map_rel (.row : Sym U Lc 1) ![.row r]).mpr ⟨r, rfl⟩
  simpa only [relMap_row_iff, Function.comp_apply, Matrix.cons_val_zero] using h

/-- The row bijection induced by an isomorphism of row assemblies. -/
noncomputable def rowEquiv
    (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) : R₁ ≃ R₂ where
  toFun r := (exists_apply_row e r).choose
  invFun r' := (exists_apply_row e.symm r').choose
  left_inv r := by
    have h1 := (exists_apply_row e r).choose_spec
    have h2 := (exists_apply_row e.symm (exists_apply_row e r).choose).choose_spec
    have h3 : Carrier.row (C := C₁)
        (exists_apply_row e.symm (exists_apply_row e r).choose).choose = .row r := by
      rw [← h2, ← h1, e.symm_apply_apply]
    exact Carrier.row.inj h3
  right_inv r' := by
    have h1 := (exists_apply_row e.symm r').choose_spec
    have h2 := (exists_apply_row e (exists_apply_row e.symm r').choose).choose_spec
    have h3 : Carrier.row (C := C₂)
        (exists_apply_row e (exists_apply_row e.symm r').choose).choose = .row r' := by
      rw [← h2, ← h1, e.apply_symm_apply]
    exact Carrier.row.inj h3

@[simp]
theorem apply_row (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) (r : R₁) :
    e (.row r) = .row (rowEquiv e r) :=
  (exists_apply_row e r).choose_spec

theorem symm_apply_row (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) (r' : R₂) :
    e.symm (.row r') = .row ((rowEquiv e).symm r') :=
  (exists_apply_row e.symm r').choose_spec

@[simp]
theorem rowEquiv_refl :
    rowEquiv (Language.Equiv.refl (lang U Lc) (Carrier R₁ C₁)) = Equiv.refl R₁ := by
  ext r
  exact Carrier.row.inj (apply_row _ r).symm

@[simp]
theorem rowEquiv_symm (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) :
    rowEquiv e.symm = (rowEquiv e).symm := by
  ext r'
  exact Carrier.row.inj ((apply_row e.symm r').symm.trans (symm_apply_row e r'))

@[simp]
theorem rowEquiv_comp {R₃ : Type*} {C₃ : R₃ → Label U → Type*}
    [∀ r τ, Lc.Structure (C₃ r τ)]
    (e₂ : Carrier R₂ C₂ ≃[lang U Lc] Carrier R₃ C₃)
    (e₁ : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) :
    rowEquiv (e₂.comp e₁) = (rowEquiv e₁).trans (rowEquiv e₂) := by
  ext r
  have h : (e₂.comp e₁) (.row r) = .row (rowEquiv e₂ (rowEquiv e₁ r)) := by
    simp only [Language.Equiv.comp_apply, apply_row]
  exact Carrier.row.inj ((apply_row (e₂.comp e₁) r).symm.trans h)

@[simp]
theorem rowEquiv_equivOfFiberEquiv (eR : R₁ ≃ R₂)
    (eF : ∀ r τ, C₁ r τ ≃[Lc] C₂ (eR r) τ) :
    rowEquiv (equivOfFiberEquiv eR eF) = eR := by
  ext r
  exact Carrier.row.inj ((apply_row (equivOfFiberEquiv eR eF) r).symm.trans
    (equivOfFiberEquiv_row eR eF r))

/-- An assembly isomorphism maps each point of fiber `(r, τ)` into fiber `(rowEquiv e r, τ)`. -/
private theorem exists_apply_pt (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂)
    (r : R₁) (τ : Label U) (x : C₁ r τ) :
    ∃ y : C₂ (rowEquiv e r) τ, e (.pt r τ x) = .pt (rowEquiv e r) τ y := by
  have hown := (e.map_rel (.own : Sym U Lc 2) ![.pt r τ x, .row r]).mpr ⟨r, τ, x, rfl, rfl⟩
  simp only [relMap_own_iff, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, apply_row] at hown
  obtain ⟨r', τ', y, hpt, hrow⟩ := hown
  obtain rfl : rowEquiv e r = r' := Carrier.row.inj hrow
  have hlab := (e.map_rel (.lab τ : Sym U Lc 1) ![.pt r τ x]).mpr ⟨r, x, rfl⟩
  simp only [relMap_lab_iff, Function.comp_apply, Matrix.cons_val_zero, hpt] at hlab
  obtain ⟨r'', y', heq⟩ := hlab
  obtain rfl : τ' = τ := by cases heq; rfl
  exact ⟨y, hpt⟩

/-- The inverse of an assembly isomorphism maps each point of fiber `(rowEquiv e r, τ)` back into
fiber `(r, τ)`. -/
private theorem exists_symm_apply_pt (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂)
    (r : R₁) (τ : Label U) (y : C₂ (rowEquiv e r) τ) :
    ∃ x : C₁ r τ, e.symm (.pt (rowEquiv e r) τ y) = .pt r τ x := by
  obtain ⟨x, hx⟩ := exists_apply_pt e.symm (rowEquiv e r) τ y
  generalize hr' : rowEquiv e.symm (rowEquiv e r) = r' at x hx
  have hrr : r' = r := by rw [← hr']; simp
  subst hrr
  exact ⟨x, hx⟩

/-- **Isomorphism restriction.** Over a relational component language, an assembly isomorphism
restricts on each fiber `(r, τ)` to an `Lc`-isomorphism
`C₁ r τ ≃[Lc] C₂ (rowEquiv e r) τ`. -/
noncomputable def fiberEquiv [Lc.IsRelational]
    (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂)
    (r : R₁) (τ : Label U) : C₁ r τ ≃[Lc] C₂ (rowEquiv e r) τ where
  toFun x := (exists_apply_pt e r τ x).choose
  invFun y := (exists_symm_apply_pt e r τ y).choose
  left_inv x := by
    have h1 := (exists_apply_pt e r τ x).choose_spec
    have h2 := (exists_symm_apply_pt e r τ (exists_apply_pt e r τ x).choose).choose_spec
    exact Carrier.pt_inj_iff.mp (h2.symm.trans ((congrArg e.symm h1).symm.trans
      (e.symm_apply_apply _)))
  right_inv y := by
    have h1 := (exists_symm_apply_pt e r τ y).choose_spec
    have h2 := (exists_apply_pt e r τ (exists_symm_apply_pt e r τ y).choose).choose_spec
    exact Carrier.pt_inj_iff.mp (h2.symm.trans ((congrArg e h1).symm.trans
      (e.apply_symm_apply _)))
  map_fun' f := isEmptyElim f
  map_rel' {n} R v := by
    cases n with
    | zero =>
      have h := e.map_rel (.lift0 R τ : Sym U Lc 1) ![.row r]
      have hcomp : e ∘ ![Carrier.row (C := C₁) r] = ![Carrier.row (rowEquiv e r)] := by
        ext t
        rw [Subsingleton.elim t 0]
        simp only [Function.comp_apply, Matrix.cons_val_zero, apply_row]
      rw [hcomp, relMap_lift0_row_iff, relMap_lift0_row_iff] at h
      simpa only [Subsingleton.elim v Fin.elim0,
        Subsingleton.elim ((fun x => (exists_apply_pt e r τ x).choose) ∘ Fin.elim0) Fin.elim0]
        using h
    | succ l =>
      have h := e.map_rel (.lift R : Sym U Lc (l + 1)) (fun i => .pt r τ (v i))
      have hcomp : e ∘ (fun i => Carrier.pt r τ (v i)) =
          fun i => Carrier.pt (rowEquiv e r) τ ((exists_apply_pt e r τ (v i)).choose) :=
        funext fun i => (exists_apply_pt e r τ (v i)).choose_spec
      rw [hcomp, relMap_lift_pt_iff, relMap_lift_pt_iff] at h
      exact h

@[simp]
theorem apply_pt [Lc.IsRelational] (e : Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂)
    (r : R₁) (τ : Label U) (x : C₁ r τ) :
    e (.pt r τ x) = .pt (rowEquiv e r) τ (fiberEquiv e r τ x) :=
  (exists_apply_pt e r τ x).choose_spec

/-- Two row assemblies over a relational component language are isomorphic exactly when there is a
bijection of rows along which corresponding fibers are isomorphic. -/
theorem nonempty_equiv_iff [Lc.IsRelational] :
    Nonempty (Carrier R₁ C₁ ≃[lang U Lc] Carrier R₂ C₂) ↔
      ∃ eR : R₁ ≃ R₂, ∀ r τ, Nonempty (C₁ r τ ≃[Lc] C₂ (eR r) τ) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨rowEquiv e, fun r τ => ⟨fiberEquiv e r τ⟩⟩
  · rintro ⟨eR, hF⟩
    exact ⟨equivOfFiberEquiv eR fun r τ => (hF r τ).some⟩

end EquivRestriction

end TauCeti.RowAssembly
